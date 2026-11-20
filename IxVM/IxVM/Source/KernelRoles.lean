import Aiur.Modules.Function

/-! # IxVM module `KernelRoles`

Role binding tables and their evidence, which name the constants the kernel treats as primitives.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module KernelRoles where

aiur_decls⟦
module KernelRoles {
  enum RoleEvidence {
      Defeq,
      Proof(Bytes::AddressRef)
    }

  enum RoleTableNode {
      Mk(Bytes::AddressRef, RoleMap<Bytes::AddressRef>, RBTreeMap::RBTreeMap<Field>, RoleMap<Lists::List<RoleEvidence>>)
    }

  type RoleTable = &RoleTableNode;

  enum RoleCtxNode {
      Mk(RoleTable, Field, RBTreeMap::RBTreeMap<Field>),
      Assumed(RoleTable, RBTreeMap::RBTreeMap<Field>)
    }

  type RoleCtx = &RoleCtxNode;

  -- Port divergence: role-indexed maps, separate from the address-keyed
  -- `RBTreeMap::RBTreeMap` (see `role_map_lookup_or_default`).
  enum RoleMap<V> {
      Nil,
      Node(Field, Field, V, &RoleMap<V>, &RoleMap<V>)
    }
}
⟧

def load_role_table := aiur_fn⟦
  fn load_role_table(binding: Bytes::AddressRef) -> RoleTable {
      let raw = (*(binding));
      let (idx, len) = IxVMCompat::io_get_info(6, raw);
      let bytes = IxByteStream::read_finite_byte_stream(6, idx, len);
      Blake3::verify_bytes_against(bytes, raw);
      let (t0, s) = IxonDeserialize::read_byte(bytes);
      assert_eq!(UInt8::to_field(t0), 232, "role table: not a binding section");
      let (t1, s) = IxonDeserialize::read_byte(s);
      assert_eq!(UInt8::to_field(t1), 3, "role table: not a binding section");
      let (version, s) = IxonDeserialize::read_byte(s);
      assert_eq!(UInt8::to_field(version), KernelRoleSpec::spec_version(),
        "role table: made for another specification version");
      let (n, s) = IxonDeserialize::read_byte(s);
      let (by_role, by_addr, _next, s) =
        read_role_bindings(s, UInt8::to_field(n), 0, RBTreeMap::RBTreeMap::Nil);
      let (m, s) = IxonDeserialize::read_byte(s);
      let (evidence, _next, s) = read_role_evidence(s, UInt8::to_field(m), 0);
      evidence_roles_have_equations(evidence);
      let Lists::Node::Nil = (*(s));
      let tbl = (&(RoleTableNode::Mk(binding, by_role, by_addr, evidence)));
      assert_basis_pinned(tbl, 0);
      tbl
    }
⟧

  -- ## The basis pin
  --
  -- The kernel installs its basis from committed records, and reads a role table only if the
  -- table binds each basis role at the committed record that declares it (the prelude's
  -- shape). The program asks the same of every table it loads: where one of these 26 roles is
  -- bound, it is bound at the address below. In role order: `Nat`, `Nat.zero`, `Nat.succ`,
  -- `Nat.rec` (0-3); `Bool`, `Bool.false`, `Bool.true`, `Bool.rec` (4-7); `Eq`, `Eq.refl`,
  -- `Eq.rec` (8-10); `PUnit`, `PUnit.unit`, `PUnit.rec` (11-13); `Empty`, `Empty.rec` (14-15);
  -- `False`, `False.rec` (16-17); `And`, `And.intro`, `And.rec` (20-22); `Quot`, `Quot.mk`,
  -- `Quot.lift`, `Quot.ind`, `Quot.sound` (32-36). Each address is the default role table's
  -- binding of the role and the address of a committed prelude record: an inductive's or a
  -- constructor's projection record, a recursor's or a quotient constant's own record, the
  -- axiom's record.

def basis_pin := aiur_fn⟦
  fn basis_pin(r: Field) -> (Field, Bytes::AddressRef) {
      match r {
        0 => {  (1, (&([UInt8::BYTE_238, UInt8::BYTE_93, UInt8::BYTE_66, UInt8::BYTE_79, UInt8::BYTE_111, UInt8::BYTE_187, UInt8::BYTE_84, UInt8::BYTE_16, UInt8::BYTE_206, UInt8::BYTE_130, UInt8::BYTE_164, UInt8::BYTE_101, UInt8::BYTE_124, UInt8::BYTE_88, UInt8::BYTE_110, UInt8::BYTE_216, UInt8::BYTE_220, UInt8::BYTE_87, UInt8::BYTE_235, UInt8::BYTE_37, UInt8::BYTE_136, UInt8::BYTE_148, UInt8::BYTE_117, UInt8::BYTE_120, UInt8::BYTE_99, UInt8::BYTE_102, UInt8::BYTE_118, UInt8::BYTE_228, UInt8::BYTE_46, UInt8::BYTE_208, UInt8::BYTE_7, UInt8::BYTE_43]))) } ,
        1 => {  (1, (&([UInt8::BYTE_9, UInt8::BYTE_133, UInt8::BYTE_26, UInt8::BYTE_4, UInt8::BYTE_34, UInt8::BYTE_161, UInt8::BYTE_136, UInt8::BYTE_34, UInt8::BYTE_68, UInt8::BYTE_125, UInt8::BYTE_151, UInt8::BYTE_133, UInt8::BYTE_18, UInt8::BYTE_59, UInt8::BYTE_70, UInt8::BYTE_190, UInt8::BYTE_29, UInt8::BYTE_83, UInt8::BYTE_241, UInt8::BYTE_162, UInt8::BYTE_208, UInt8::BYTE_19, UInt8::BYTE_121, UInt8::BYTE_146, UInt8::BYTE_254, UInt8::BYTE_22, UInt8::BYTE_174, UInt8::BYTE_105, UInt8::BYTE_60, UInt8::BYTE_179, UInt8::BYTE_240, UInt8::BYTE_125]))) } ,
        2 => {  (1, (&([UInt8::BYTE_117, UInt8::BYTE_124, UInt8::BYTE_169, UInt8::BYTE_221, UInt8::BYTE_187, UInt8::BYTE_253, UInt8::BYTE_252, UInt8::BYTE_185, UInt8::BYTE_57, UInt8::BYTE_164, UInt8::BYTE_44, UInt8::BYTE_22, UInt8::BYTE_76, UInt8::BYTE_67, UInt8::BYTE_93, UInt8::BYTE_237, UInt8::BYTE_230, UInt8::BYTE_214, UInt8::BYTE_210, UInt8::BYTE_52, UInt8::BYTE_39, UInt8::BYTE_159, UInt8::BYTE_137, UInt8::BYTE_225, UInt8::BYTE_209, UInt8::BYTE_54, UInt8::BYTE_104, UInt8::BYTE_243, UInt8::BYTE_239, UInt8::BYTE_77, UInt8::BYTE_137, UInt8::BYTE_29]))) } ,
        3 => {  (1, (&([UInt8::BYTE_163, UInt8::BYTE_125, UInt8::BYTE_40, UInt8::BYTE_162, UInt8::BYTE_42, UInt8::BYTE_2, UInt8::BYTE_205, UInt8::BYTE_51, UInt8::BYTE_179, UInt8::BYTE_200, UInt8::BYTE_115, UInt8::BYTE_128, UInt8::BYTE_244, UInt8::BYTE_92, UInt8::BYTE_137, UInt8::BYTE_144, UInt8::BYTE_201, UInt8::BYTE_92, UInt8::BYTE_206, UInt8::BYTE_83, UInt8::BYTE_241, UInt8::BYTE_84, UInt8::BYTE_173, UInt8::BYTE_51, UInt8::BYTE_42, UInt8::BYTE_156, UInt8::BYTE_181, UInt8::BYTE_249, UInt8::BYTE_177, UInt8::BYTE_99, UInt8::BYTE_135, UInt8::BYTE_83]))) } ,
        4 => {  (1, (&([UInt8::BYTE_119, UInt8::BYTE_219, UInt8::BYTE_130, UInt8::BYTE_215, UInt8::BYTE_5, UInt8::BYTE_42, UInt8::BYTE_96, UInt8::BYTE_110, UInt8::BYTE_170, UInt8::BYTE_243, UInt8::BYTE_36, UInt8::BYTE_137, UInt8::BYTE_49, UInt8::BYTE_97, UInt8::BYTE_214, UInt8::BYTE_152, UInt8::BYTE_144, UInt8::BYTE_73, UInt8::BYTE_239, UInt8::BYTE_78, UInt8::BYTE_15, UInt8::BYTE_57, UInt8::BYTE_62, UInt8::BYTE_47, UInt8::BYTE_233, UInt8::BYTE_237, UInt8::BYTE_175, UInt8::BYTE_82, UInt8::BYTE_244, UInt8::BYTE_34, UInt8::BYTE_94, UInt8::BYTE_216]))) } ,
        5 => {  (1, (&([UInt8::BYTE_165, UInt8::BYTE_252, UInt8::BYTE_133, UInt8::BYTE_109, UInt8::BYTE_230, UInt8::BYTE_53, UInt8::BYTE_207, UInt8::BYTE_196, UInt8::BYTE_10, UInt8::BYTE_183, UInt8::BYTE_3, UInt8::BYTE_238, UInt8::BYTE_165, UInt8::BYTE_28, UInt8::BYTE_183, UInt8::BYTE_4, UInt8::BYTE_220, UInt8::BYTE_230, UInt8::BYTE_152, UInt8::BYTE_95, UInt8::BYTE_215, UInt8::BYTE_222, UInt8::BYTE_146, UInt8::BYTE_31, UInt8::BYTE_148, UInt8::BYTE_184, UInt8::BYTE_214, UInt8::BYTE_53, UInt8::BYTE_233, UInt8::BYTE_211, UInt8::BYTE_102, UInt8::BYTE_127]))) } ,
        6 => {  (1, (&([UInt8::BYTE_239, UInt8::BYTE_21, UInt8::BYTE_100, UInt8::BYTE_99, UInt8::BYTE_165, UInt8::BYTE_39, UInt8::BYTE_191, UInt8::BYTE_210, UInt8::BYTE_54, UInt8::BYTE_71, UInt8::BYTE_46, UInt8::BYTE_96, UInt8::BYTE_107, UInt8::BYTE_44, UInt8::BYTE_205, UInt8::BYTE_223, UInt8::BYTE_115, UInt8::BYTE_244, UInt8::BYTE_88, UInt8::BYTE_81, UInt8::BYTE_149, UInt8::BYTE_227, UInt8::BYTE_101, UInt8::BYTE_224, UInt8::BYTE_67, UInt8::BYTE_14, UInt8::BYTE_227, UInt8::BYTE_194, UInt8::BYTE_9, UInt8::BYTE_33, UInt8::BYTE_216, UInt8::BYTE_204]))) } ,
        7 => {  (1, (&([UInt8::BYTE_105, UInt8::BYTE_227, UInt8::BYTE_8, UInt8::BYTE_65, UInt8::BYTE_57, UInt8::BYTE_249, UInt8::BYTE_243, UInt8::BYTE_250, UInt8::BYTE_1, UInt8::BYTE_156, UInt8::BYTE_179, UInt8::BYTE_44, UInt8::BYTE_24, UInt8::BYTE_138, UInt8::BYTE_218, UInt8::BYTE_4, UInt8::BYTE_211, UInt8::BYTE_81, UInt8::BYTE_151, UInt8::BYTE_146, UInt8::BYTE_93, UInt8::BYTE_220, UInt8::BYTE_117, UInt8::BYTE_105, UInt8::BYTE_96, UInt8::BYTE_210, UInt8::BYTE_5, UInt8::BYTE_213, UInt8::BYTE_12, UInt8::BYTE_84, UInt8::BYTE_42, UInt8::BYTE_232]))) } ,
        8 => {  (1, (&([UInt8::BYTE_157, UInt8::BYTE_60, UInt8::BYTE_123, UInt8::BYTE_207, UInt8::BYTE_204, UInt8::BYTE_143, UInt8::BYTE_31, UInt8::BYTE_22, UInt8::BYTE_97, UInt8::BYTE_188, UInt8::BYTE_232, UInt8::BYTE_125, UInt8::BYTE_55, UInt8::BYTE_26, UInt8::BYTE_93, UInt8::BYTE_160, UInt8::BYTE_213, UInt8::BYTE_24, UInt8::BYTE_140, UInt8::BYTE_27, UInt8::BYTE_192, UInt8::BYTE_93, UInt8::BYTE_239, UInt8::BYTE_33, UInt8::BYTE_212, UInt8::BYTE_170, UInt8::BYTE_23, UInt8::BYTE_97, UInt8::BYTE_56, UInt8::BYTE_201, UInt8::BYTE_27, UInt8::BYTE_16]))) } ,
        9 => {  (1, (&([UInt8::BYTE_84, UInt8::BYTE_176, UInt8::BYTE_61, UInt8::BYTE_237, UInt8::BYTE_207, UInt8::BYTE_208, UInt8::BYTE_182, UInt8::BYTE_145, UInt8::BYTE_14, UInt8::BYTE_4, UInt8::BYTE_235, UInt8::BYTE_6, UInt8::BYTE_228, UInt8::BYTE_2, UInt8::BYTE_238, UInt8::BYTE_40, UInt8::BYTE_90, UInt8::BYTE_218, UInt8::BYTE_207, UInt8::BYTE_207, UInt8::BYTE_56, UInt8::BYTE_139, UInt8::BYTE_44, UInt8::BYTE_249, UInt8::BYTE_36, UInt8::BYTE_171, UInt8::BYTE_227, UInt8::BYTE_178, UInt8::BYTE_8, UInt8::BYTE_224, UInt8::BYTE_123, UInt8::BYTE_72]))) } ,
        10 => {  (1, (&([UInt8::BYTE_11, UInt8::BYTE_185, UInt8::BYTE_20, UInt8::BYTE_221, UInt8::BYTE_56, UInt8::BYTE_223, UInt8::BYTE_206, UInt8::BYTE_142, UInt8::BYTE_218, UInt8::BYTE_164, UInt8::BYTE_35, UInt8::BYTE_44, UInt8::BYTE_84, UInt8::BYTE_144, UInt8::BYTE_92, UInt8::BYTE_161, UInt8::BYTE_94, UInt8::BYTE_163, UInt8::BYTE_132, UInt8::BYTE_193, UInt8::BYTE_4, UInt8::BYTE_35, UInt8::BYTE_226, UInt8::BYTE_129, UInt8::BYTE_206, UInt8::BYTE_110, UInt8::BYTE_93, UInt8::BYTE_243, UInt8::BYTE_84, UInt8::BYTE_210, UInt8::BYTE_150, UInt8::BYTE_92]))) } ,
        11 => {  (1, (&([UInt8::BYTE_31, UInt8::BYTE_36, UInt8::BYTE_179, UInt8::BYTE_69, UInt8::BYTE_4, UInt8::BYTE_94, UInt8::BYTE_131, UInt8::BYTE_3, UInt8::BYTE_61, UInt8::BYTE_197, UInt8::BYTE_115, UInt8::BYTE_66, UInt8::BYTE_205, UInt8::BYTE_211, UInt8::BYTE_189, UInt8::BYTE_40, UInt8::BYTE_66, UInt8::BYTE_209, UInt8::BYTE_195, UInt8::BYTE_162, UInt8::BYTE_192, UInt8::BYTE_75, UInt8::BYTE_25, UInt8::BYTE_60, UInt8::BYTE_64, UInt8::BYTE_152, UInt8::BYTE_115, UInt8::BYTE_190, UInt8::BYTE_203, UInt8::BYTE_117, UInt8::BYTE_180, UInt8::BYTE_20]))) } ,
        12 => {  (1, (&([UInt8::BYTE_165, UInt8::BYTE_137, UInt8::BYTE_154, UInt8::BYTE_97, UInt8::BYTE_138, UInt8::BYTE_94, UInt8::BYTE_199, UInt8::BYTE_185, UInt8::BYTE_223, UInt8::BYTE_6, UInt8::BYTE_178, UInt8::BYTE_217, UInt8::BYTE_209, UInt8::BYTE_13, UInt8::BYTE_236, UInt8::BYTE_115, UInt8::BYTE_250, UInt8::BYTE_96, UInt8::BYTE_253, UInt8::BYTE_212, UInt8::BYTE_189, UInt8::BYTE_170, UInt8::BYTE_89, UInt8::BYTE_32, UInt8::BYTE_77, UInt8::BYTE_138, UInt8::BYTE_76, UInt8::BYTE_107, UInt8::BYTE_19, UInt8::BYTE_234, UInt8::BYTE_34, UInt8::BYTE_114]))) } ,
        13 => {  (1, (&([UInt8::BYTE_87, UInt8::BYTE_47, UInt8::BYTE_254, UInt8::BYTE_188, UInt8::BYTE_254, UInt8::BYTE_189, UInt8::BYTE_72, UInt8::BYTE_56, UInt8::BYTE_51, UInt8::BYTE_201, UInt8::BYTE_149, UInt8::BYTE_128, UInt8::BYTE_54, UInt8::BYTE_93, UInt8::BYTE_108, UInt8::BYTE_173, UInt8::BYTE_90, UInt8::BYTE_250, UInt8::BYTE_184, UInt8::BYTE_223, UInt8::BYTE_112, UInt8::BYTE_92, UInt8::BYTE_21, UInt8::BYTE_17, UInt8::BYTE_238, UInt8::BYTE_40, UInt8::BYTE_132, UInt8::BYTE_68, UInt8::BYTE_173, UInt8::BYTE_198, UInt8::BYTE_118, UInt8::BYTE_185]))) } ,
        14 => {  (1, (&([UInt8::BYTE_200, UInt8::BYTE_113, UInt8::BYTE_200, UInt8::BYTE_114, UInt8::BYTE_197, UInt8::BYTE_245, UInt8::BYTE_219, UInt8::BYTE_243, UInt8::BYTE_3, UInt8::BYTE_43, UInt8::BYTE_90, UInt8::BYTE_178, UInt8::BYTE_28, UInt8::BYTE_85, UInt8::BYTE_22, UInt8::BYTE_57, UInt8::BYTE_207, UInt8::BYTE_18, UInt8::BYTE_171, UInt8::BYTE_217, UInt8::BYTE_210, UInt8::BYTE_225, UInt8::BYTE_77, UInt8::BYTE_69, UInt8::BYTE_114, UInt8::BYTE_78, UInt8::BYTE_185, UInt8::BYTE_122, UInt8::BYTE_89, UInt8::BYTE_117, UInt8::BYTE_251, UInt8::BYTE_147]))) } ,
        15 => {  (1, (&([UInt8::BYTE_57, UInt8::BYTE_63, UInt8::BYTE_142, UInt8::BYTE_173, UInt8::BYTE_104, UInt8::BYTE_3, UInt8::BYTE_131, UInt8::BYTE_19, UInt8::BYTE_190, UInt8::BYTE_209, UInt8::BYTE_138, UInt8::BYTE_152, UInt8::BYTE_17, UInt8::BYTE_87, UInt8::BYTE_178, UInt8::BYTE_136, UInt8::BYTE_107, UInt8::BYTE_194, UInt8::BYTE_182, UInt8::BYTE_227, UInt8::BYTE_228, UInt8::BYTE_243, UInt8::BYTE_172, UInt8::BYTE_224, UInt8::BYTE_55, UInt8::BYTE_218, UInt8::BYTE_36, UInt8::BYTE_125, UInt8::BYTE_73, UInt8::BYTE_53, UInt8::BYTE_42, UInt8::BYTE_76]))) } ,
        16 => {  (1, (&([UInt8::BYTE_206, UInt8::BYTE_119, UInt8::BYTE_72, UInt8::BYTE_125, UInt8::BYTE_84, UInt8::BYTE_147, UInt8::BYTE_216, UInt8::BYTE_231, UInt8::BYTE_36, UInt8::BYTE_239, UInt8::BYTE_3, UInt8::BYTE_103, UInt8::BYTE_125, UInt8::BYTE_170, UInt8::BYTE_235, UInt8::BYTE_93, UInt8::BYTE_68, UInt8::BYTE_4, UInt8::BYTE_9, UInt8::BYTE_15, UInt8::BYTE_124, UInt8::BYTE_18, UInt8::BYTE_184, UInt8::BYTE_239, UInt8::BYTE_203, UInt8::BYTE_85, UInt8::BYTE_124, UInt8::BYTE_147, UInt8::BYTE_163, UInt8::BYTE_107, UInt8::BYTE_207, UInt8::BYTE_82]))) } ,
        17 => {  (1, (&([UInt8::BYTE_12, UInt8::BYTE_157, UInt8::BYTE_146, UInt8::BYTE_76, UInt8::BYTE_234, UInt8::BYTE_173, UInt8::BYTE_212, UInt8::BYTE_107, UInt8::BYTE_126, UInt8::BYTE_17, UInt8::BYTE_75, UInt8::BYTE_35, UInt8::BYTE_40, UInt8::BYTE_118, UInt8::BYTE_116, UInt8::BYTE_246, UInt8::BYTE_227, UInt8::BYTE_27, UInt8::BYTE_176, UInt8::BYTE_15, UInt8::BYTE_223, UInt8::BYTE_134, UInt8::BYTE_180, UInt8::BYTE_250, UInt8::BYTE_183, UInt8::BYTE_250, UInt8::BYTE_183, UInt8::BYTE_104, UInt8::BYTE_40, UInt8::BYTE_4, UInt8::BYTE_200, UInt8::BYTE_178]))) } ,
        20 => {  (1, (&([UInt8::BYTE_79, UInt8::BYTE_73, UInt8::BYTE_42, UInt8::BYTE_148, UInt8::BYTE_176, UInt8::BYTE_248, UInt8::BYTE_146, UInt8::BYTE_206, UInt8::BYTE_220, UInt8::BYTE_196, UInt8::BYTE_157, UInt8::BYTE_44, UInt8::BYTE_13, UInt8::BYTE_99, UInt8::BYTE_43, UInt8::BYTE_181, UInt8::BYTE_15, UInt8::BYTE_235, UInt8::BYTE_246, UInt8::BYTE_253, UInt8::BYTE_120, UInt8::BYTE_231, UInt8::BYTE_192, UInt8::BYTE_166, UInt8::BYTE_136, UInt8::BYTE_97, UInt8::BYTE_1, UInt8::BYTE_152, UInt8::BYTE_204, UInt8::BYTE_20, UInt8::BYTE_142, UInt8::BYTE_49]))) } ,
        21 => {  (1, (&([UInt8::BYTE_151, UInt8::BYTE_147, UInt8::BYTE_60, UInt8::BYTE_16, UInt8::BYTE_155, UInt8::BYTE_196, UInt8::BYTE_138, UInt8::BYTE_178, UInt8::BYTE_82, UInt8::BYTE_58, UInt8::BYTE_77, UInt8::BYTE_177, UInt8::BYTE_251, UInt8::BYTE_237, UInt8::BYTE_119, UInt8::BYTE_99, UInt8::BYTE_199, UInt8::BYTE_144, UInt8::BYTE_50, UInt8::BYTE_83, UInt8::BYTE_95, UInt8::BYTE_255, UInt8::BYTE_228, UInt8::BYTE_135, UInt8::BYTE_178, UInt8::BYTE_205, UInt8::BYTE_121, UInt8::BYTE_139, UInt8::BYTE_40, UInt8::BYTE_161, UInt8::BYTE_234, UInt8::BYTE_95]))) } ,
        22 => {  (1, (&([UInt8::BYTE_244, UInt8::BYTE_229, UInt8::BYTE_147, UInt8::BYTE_204, UInt8::BYTE_38, UInt8::BYTE_9, UInt8::BYTE_152, UInt8::BYTE_78, UInt8::BYTE_207, UInt8::BYTE_107, UInt8::BYTE_4, UInt8::BYTE_110, UInt8::BYTE_217, UInt8::BYTE_122, UInt8::BYTE_66, UInt8::BYTE_240, UInt8::BYTE_236, UInt8::BYTE_218, UInt8::BYTE_251, UInt8::BYTE_48, UInt8::BYTE_24, UInt8::BYTE_221, UInt8::BYTE_169, UInt8::BYTE_240, UInt8::BYTE_209, UInt8::BYTE_155, UInt8::BYTE_178, UInt8::BYTE_125, UInt8::BYTE_218, UInt8::BYTE_110, UInt8::BYTE_223, UInt8::BYTE_3]))) } ,
        32 => {  (1, (&([UInt8::BYTE_200, UInt8::BYTE_123, UInt8::BYTE_41, UInt8::BYTE_147, UInt8::BYTE_28, UInt8::BYTE_228, UInt8::BYTE_224, UInt8::BYTE_2, UInt8::BYTE_66, UInt8::BYTE_95, UInt8::BYTE_133, UInt8::BYTE_102, UInt8::BYTE_209, UInt8::BYTE_203, UInt8::BYTE_240, UInt8::BYTE_18, UInt8::BYTE_203, UInt8::BYTE_149, UInt8::BYTE_56, UInt8::BYTE_63, UInt8::BYTE_126, UInt8::BYTE_124, UInt8::BYTE_195, UInt8::BYTE_83, UInt8::BYTE_63, UInt8::BYTE_87, UInt8::BYTE_99, UInt8::BYTE_214, UInt8::BYTE_59, UInt8::BYTE_63, UInt8::BYTE_32, UInt8::BYTE_96]))) } ,
        33 => {  (1, (&([UInt8::BYTE_179, UInt8::BYTE_142, UInt8::BYTE_110, UInt8::BYTE_198, UInt8::BYTE_61, UInt8::BYTE_58, UInt8::BYTE_198, UInt8::BYTE_202, UInt8::BYTE_164, UInt8::BYTE_86, UInt8::BYTE_175, UInt8::BYTE_105, UInt8::BYTE_143, UInt8::BYTE_250, UInt8::BYTE_248, UInt8::BYTE_102, UInt8::BYTE_225, UInt8::BYTE_146, UInt8::BYTE_189, UInt8::BYTE_62, UInt8::BYTE_132, UInt8::BYTE_216, UInt8::BYTE_9, UInt8::BYTE_42, UInt8::BYTE_132, UInt8::BYTE_21, UInt8::BYTE_183, UInt8::BYTE_147, UInt8::BYTE_167, UInt8::BYTE_171, UInt8::BYTE_181, UInt8::BYTE_152]))) } ,
        34 => {  (1, (&([UInt8::BYTE_171, UInt8::BYTE_187, UInt8::BYTE_156, UInt8::BYTE_7, UInt8::BYTE_178, UInt8::BYTE_196, UInt8::BYTE_102, UInt8::BYTE_237, UInt8::BYTE_99, UInt8::BYTE_0, UInt8::BYTE_135, UInt8::BYTE_132, UInt8::BYTE_40, UInt8::BYTE_68, UInt8::BYTE_234, UInt8::BYTE_4, UInt8::BYTE_100, UInt8::BYTE_185, UInt8::BYTE_92, UInt8::BYTE_160, UInt8::BYTE_33, UInt8::BYTE_139, UInt8::BYTE_42, UInt8::BYTE_30, UInt8::BYTE_230, UInt8::BYTE_121, UInt8::BYTE_7, UInt8::BYTE_84, UInt8::BYTE_45, UInt8::BYTE_68, UInt8::BYTE_48, UInt8::BYTE_132]))) } ,
        35 => {  (1, (&([UInt8::BYTE_44, UInt8::BYTE_5, UInt8::BYTE_242, UInt8::BYTE_131, UInt8::BYTE_164, UInt8::BYTE_80, UInt8::BYTE_160, UInt8::BYTE_87, UInt8::BYTE_187, UInt8::BYTE_103, UInt8::BYTE_160, UInt8::BYTE_180, UInt8::BYTE_66, UInt8::BYTE_37, UInt8::BYTE_244, UInt8::BYTE_120, UInt8::BYTE_194, UInt8::BYTE_208, UInt8::BYTE_15, UInt8::BYTE_187, UInt8::BYTE_253, UInt8::BYTE_151, UInt8::BYTE_40, UInt8::BYTE_180, UInt8::BYTE_248, UInt8::BYTE_206, UInt8::BYTE_246, UInt8::BYTE_192, UInt8::BYTE_243, UInt8::BYTE_85, UInt8::BYTE_60, UInt8::BYTE_253]))) } ,
        36 => {  (1, (&([UInt8::BYTE_132, UInt8::BYTE_246, UInt8::BYTE_186, UInt8::BYTE_212, UInt8::BYTE_18, UInt8::BYTE_241, UInt8::BYTE_180, UInt8::BYTE_234, UInt8::BYTE_67, UInt8::BYTE_150, UInt8::BYTE_160, UInt8::BYTE_196, UInt8::BYTE_209, UInt8::BYTE_94, UInt8::BYTE_239, UInt8::BYTE_194, UInt8::BYTE_141, UInt8::BYTE_48, UInt8::BYTE_120, UInt8::BYTE_82, UInt8::BYTE_27, UInt8::BYTE_240, UInt8::BYTE_6, UInt8::BYTE_33, UInt8::BYTE_207, UInt8::BYTE_187, UInt8::BYTE_250, UInt8::BYTE_91, UInt8::BYTE_47, UInt8::BYTE_228, UInt8::BYTE_57, UInt8::BYTE_207]))) } ,
        _ => {  (0, (&([UInt8::BYTE_0; 32]))) } ,
      }
    }
⟧


  -- Every pinned role from `r` on that the table binds is bound at its pin.

def assert_basis_pinned := aiur_fn⟦
  fn assert_basis_pinned(tbl: RoleTable, r: Field) -> () {
      match r - (KernelRoleSpec::role_quot_sound() + 1) {
        0 => {  () } ,
        _ => {
          let (pinned, want) = basis_pin(r);
          match pinned * role_is_bound(tbl, r) {
            1 => {
              assert_eq!(Bytes::address_eq(role_bound_addr_or_zero(tbl, r), want), 1,
                "role table: a basis role is not bound at its committed record");
              () } ,
            _ => {  () } ,
          };
          assert_basis_pinned(tbl, r + 1) } ,
      }
    }
⟧

  -- A recursor whose family is one of the basis families (`Nat`, `Eq`, `PUnit`, `Empty`,
  -- `False`: roles 0, 8, 11, 14, 16, the families whose meaning the certified kernel fixes by
  -- hand) is that family's committed recursor record (roles 3, 10, 13, 15, 17). The generated
  -- comparison fixes a recursor's type and rules, not its record's bytes, so without this a
  -- basis family would have recursor records at other addresses. The pins are constants, so
  -- the check is the same in a validating and in an assumed context.

def basis_rec_at_pin := aiur_fn⟦
  fn basis_rec_at_pin(parent: Bytes::AddressRef, addr: Bytes::AddressRef) -> () {
      basis_rec_pair(parent, addr, 0, 3);
      basis_rec_pair(parent, addr, 8, 10);
      basis_rec_pair(parent, addr, 11, 13);
      basis_rec_pair(parent, addr, 14, 15);
      basis_rec_pair(parent, addr, 16, 17)
    }
⟧

def basis_rec_pair := aiur_fn⟦
  fn basis_rec_pair(parent: Bytes::AddressRef, addr: Bytes::AddressRef, family: Field, recursor: Field) -> () {
      let (_, family_pin) = basis_pin(family);
      match Bytes::address_eq(parent, family_pin) {
        1 => {
          let (_, recursor_pin) = basis_pin(recursor);
          assert_eq!(Bytes::address_eq(addr, recursor_pin), 1,
            "a recursor of a basis family is not the family's committed recursor");
          () } ,
        _ => {  () } ,
      }
    }
⟧

  -- An evidence entry is for a role with equations: an operation or a definition role
  -- whose specification lists at least one (the kernel's `RoleTable.check`: `evidence for
  -- a role which has no equations`). A role without them has no entry, not an empty one.

def evidence_roles_have_equations := aiur_fn⟦
  fn evidence_roles_have_equations(ev: RoleMap<Lists::List<RoleEvidence>>) -> () {
      match ev {
        RoleMap::Nil => {  () } ,
        RoleMap::Node(_, r, _, left, right) => {
          assert_eq!(Fields::is_zero(KernelRoleSpec::op_equation_count(r) + KernelRoleSpec::eqns_equation_count(r)), 0,
            "role table: evidence for a role with no equations");
          evidence_roles_have_equations((*(left)));
          evidence_roles_have_equations((*(right))) } ,
      }
    }
⟧

def read_role_bindings := aiur_fn⟦
  fn read_role_bindings(s: Bytes::Stream, count: Field, next: Field, by_addr: RBTreeMap::RBTreeMap<Field>)
        -> (RoleMap<Bytes::AddressRef>, RBTreeMap::RBTreeMap<Field>, Field, Bytes::Stream) {
      match count {
        0 => {  (RoleMap::Nil, by_addr, next, s) } ,
        _ => {
          let [b0, _, _, _, _, _, _, _] = UInt8::raw_bit_decomposition(count);
          let half = (count - b0) / 2;
          let (left, by_addr, next, s) = read_role_bindings(s, half, next, by_addr);
          let (rb, s) = IxonDeserialize::read_byte(s);
          let r = UInt8::to_field(rb);
          assert_eq!(UInt32::less_than_fields(r, KernelRoleSpec::role_count()), 1, "role table: unknown role");
          assert_eq!(UInt32::less_than_fields(r, next), 0, "role table: roles out of order");
          let (a, s) = IxonDeserialize::get_address(s);
          assert_eq!(RBTreeMap::rbtree_map_lookup_or_default(a, by_addr, 0), 0,
            "role table: an address is bound to two roles");
          let by_addr = RBTreeMap::rbtree_map_insert(a, r + 1, by_addr);
          let (right, by_addr, next, s) =
            read_role_bindings(s, count - (half + 1), r + 1, by_addr);
          (RoleMap::Node(1, r, a, (&(left)), (&(right))), by_addr, next, s) } ,
      }
    }
⟧

def read_role_evidence := aiur_fn⟦
  fn read_role_evidence(s: Bytes::Stream, count: Field, next: Field)
        -> (RoleMap<Lists::List<RoleEvidence>>, Field, Bytes::Stream) {
      match count {
        0 => {  (RoleMap::Nil, next, s) } ,
        _ => {
          let [b0, _, _, _, _, _, _, _] = UInt8::raw_bit_decomposition(count);
          let half = (count - b0) / 2;
          let (left, next, s) = read_role_evidence(s, half, next);
          let (rb, s) = IxonDeserialize::read_byte(s);
          let r = UInt8::to_field(rb);
          assert_eq!(UInt32::less_than_fields(r, KernelRoleSpec::role_count()), 1, "role table: unknown role");
          assert_eq!(UInt32::less_than_fields(r, next), 0, "role table: evidence out of order");
          let (kb, s) = IxonDeserialize::read_byte(s);
          let (entries, s) = read_evidence_entries(s, UInt8::to_field(kb));
          let (right, next, s) = read_role_evidence(s, count - (half + 1), r + 1);
          (RoleMap::Node(1, r, entries, (&(left)), (&(right))), next, s) } ,
      }
    }
⟧

def read_evidence_entries := aiur_fn⟦
  fn read_evidence_entries(s: Bytes::Stream, count: Field) -> (Lists::List<RoleEvidence>, Bytes::Stream) {
      match count {
        0 => {  ((&(Lists::Node::Nil)), s) } ,
        _ => {
          let (tag, s) = IxonDeserialize::read_byte(s);
          match UInt8::to_field(tag) {
            0 => {
              let (rest, s) = read_evidence_entries(s, count - 1);
              ((&(Lists::Node::Cons(RoleEvidence::Defeq, rest))), s) } ,
            1 => {
              let (a, s) = IxonDeserialize::get_address(s);
              let (rest, s) = read_evidence_entries(s, count - 1);
              ((&(Lists::Node::Cons(RoleEvidence::Proof(a), rest))), s) } ,
          } } ,
      }
    }
⟧

def role_ctx_assumed := aiur_fn⟦
  fn role_ctx_assumed(binding: Bytes::AddressRef) -> RoleCtx {
      (&(RoleCtxNode::Assumed(load_role_table(binding), RBTreeMap::RBTreeMap::Nil)))
    }
⟧

def role_ctx_for_validator := aiur_fn⟦
  fn role_ctx_for_validator(binding: Bytes::AddressRef, validator: Field) -> RoleCtx {
      load_role_ctx(binding, validator, Options::Option::None)
    }
⟧

def validate_user_axioms := aiur_fn⟦
  fn validate_user_axioms(tbl: RoleTable, leaves: Lists::List<Bytes::AddressRef>, acc: RBTreeMap::RBTreeMap<Field>)
        -> RBTreeMap::RBTreeMap<Field> {
      match (*(leaves)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(a, rest) => {
          assert_eq!(RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0), 0,
            "claim: user axiom is bound in the role table");
          match (*(Ingress::get_ci(a))) {
            KernelTypes::KConstantInfo::Axiom(nl, ty, u) => {
              assert_eq!(u, 0, "claim: user axiom is unsafe");
              assert_not_axiom_spec(tbl, nl, ty);
              validate_user_axioms(tbl, rest, RBTreeMap::rbtree_map_insert(a, 1, acc)) } ,
            _ => {
              assert_eq!(0, 1, "claim: axioms tree entry is not an axiom");
              acc } ,
          } } ,
      }
    }
⟧

  -- A user axiom may not restate the specification of an axiom role (`propext`,
  -- `Classical.choice`, `sorryAx`, and `Quot.sound` where the table binds it): the same level
  -- count and the same type once every binder datum is erased (the kernel's `axiomRoleSpecHit?`,
  -- `ConstantVal.matchesPin`). Such an axiom is the role's own under another address.

def assert_not_axiom_spec := aiur_fn⟦
  fn assert_not_axiom_spec(tbl: RoleTable, nl: Field, ty: KernelTypes::KExpr) -> () {
      assert_eq!(restates_role(tbl, nl, ty, KernelRoleSpec::role_propext()), 0,
        "claim: a user axiom restates an axiom role's specification");
      assert_eq!(restates_role(tbl, nl, ty, KernelRoleSpec::role_choice()), 0,
        "claim: a user axiom restates an axiom role's specification");
      assert_eq!(restates_role(tbl, nl, ty, KernelRoleSpec::role_sorry_ax()), 0,
        "claim: a user axiom restates an axiom role's specification");
      match role_is_bound(tbl, KernelRoleSpec::role_quot_sound()) {
        1 => {
          assert_eq!(restates_role(tbl, nl, ty, KernelRoleSpec::role_quot_sound()), 0,
            "claim: a user axiom restates an axiom role's specification");
          () } ,
        _ => {  () } ,
      }
    }
⟧

def restates_role := aiur_fn⟦
  fn restates_role(tbl: RoleTable, nl: Field, ty: KernelTypes::KExpr, r: Field) -> Field {
      match nl - KernelRoleSpec::role_levels(r) {
        0 => {
          KernelCheck::kexpr_struct_eq(erase_data(ty), erase_data(KernelRoleSpec::role_type(tbl, r))) } ,
        _ => {  0 } ,
      }
    }
⟧

  -- Every binder datum set to never zero (the kernel's `Expr.erasePw`).

def erase_data := aiur_fn⟦
  fn erase_data(e: KernelTypes::KExpr) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::App(f, a) => {
          (&(KernelTypes::KExprNode::App(erase_data(f), erase_data(a)))) } ,
        KernelTypes::KExprNode::Lam(t, b, _) => {
          (&(KernelTypes::KExprNode::Lam(erase_data(t), erase_data(b),
            (&(KernelTypes::KLevelNode::Succ((&(KernelTypes::KLevelNode::Zero)))))))) } ,
        KernelTypes::KExprNode::Forall(t, b, _) => {
          (&(KernelTypes::KExprNode::Forall(erase_data(t), erase_data(b),
            (&(KernelTypes::KLevelNode::Succ((&(KernelTypes::KLevelNode::Zero)))))))) } ,
        KernelTypes::KExprNode::Let(t, v, b) => {
          (&(KernelTypes::KExprNode::Let(erase_data(t), erase_data(v), erase_data(b)))) } ,
        KernelTypes::KExprNode::Proj(s, i, x) => {
          (&(KernelTypes::KExprNode::Proj(s, i, erase_data(x)))) } ,
        _ => {  e } ,
      }
    }
⟧

  -- A claim with user axioms needs the table to bind `propext`, `Classical.choice` and
  -- `sorryAx`: an unbound one's own axiom is an unbound safe axiom, which the claim could
  -- otherwise list as a user axiom (the kernel's admission of a table under user axioms).

def assert_axiom_roles_bound := aiur_fn⟦
  fn assert_axiom_roles_bound(tbl: RoleTable) -> () {
      assert_eq!(role_is_bound(tbl, KernelRoleSpec::role_propext()), 1,
        "claim: user axioms need propext, Classical.choice and sorryAx bound");
      assert_eq!(role_is_bound(tbl, KernelRoleSpec::role_choice()), 1,
        "claim: user axioms need propext, Classical.choice and sorryAx bound");
      assert_eq!(role_is_bound(tbl, KernelRoleSpec::role_sorry_ax()), 1,
        "claim: user axioms need propext, Classical.choice and sorryAx bound");
      ()
    }
⟧

def load_role_ctx := aiur_fn⟦
  fn load_role_ctx(binding: Bytes::AddressRef, validator: Field, axioms_opt: Options::Option<Bytes::AddressRef>) -> RoleCtx {
      let tbl = load_role_table(binding);
      let axioms = match axioms_opt {
        Options::Option::None => {  RBTreeMap::RBTreeMap::Nil } ,
        Options::Option::Some(ax_root) => {
          assert_axiom_roles_bound(tbl);
          validate_user_axioms(tbl, KernelClaim::load_assumption_tree(ax_root), RBTreeMap::RBTreeMap::Nil) } ,
      };
      match validator {
        3 => {  (&(RoleCtxNode::Mk(tbl, KernelRoleSpec::group_count(), axioms))) } ,
        4 => {  (&(RoleCtxNode::Assumed(tbl, axioms))) } ,
        _ => {
          assert_eq!(0, 1, "claim: wrong validator identity");
          (&(RoleCtxNode::Mk(tbl, KernelRoleSpec::group_count(), axioms))) } ,
      }
    }
⟧

def role_ctx_validator := aiur_fn⟦
  fn role_ctx_validator(rc: RoleCtx) -> Field {
      3 + role_ctx_is_assumed(rc)
    }
⟧

def role_ctx_table := aiur_fn⟦
  fn role_ctx_table(rc: RoleCtx) -> RoleTable {
      match (*(rc)) {
        RoleCtxNode::Mk(tbl, _, _) => {  tbl } ,
        RoleCtxNode::Assumed(tbl, _) => {  tbl } ,
      }
    }
⟧

def role_ctx_axioms := aiur_fn⟦
  fn role_ctx_axioms(rc: RoleCtx) -> RBTreeMap::RBTreeMap<Field> {
      match (*(rc)) {
        RoleCtxNode::Mk(_, _, axioms) => {  axioms } ,
        RoleCtxNode::Assumed(_, axioms) => {  axioms } ,
      }
    }
⟧

def role_ctx_is_assumed := aiur_fn⟦
  fn role_ctx_is_assumed(rc: RoleCtx) -> Field {
      match (*(rc)) {
        RoleCtxNode::Mk(_, _, _) => {  0 } ,
        RoleCtxNode::Assumed(_, _) => {  1 } ,
      }
    }
⟧

  -- Whether `rc` is a group's validation context: a validating context whose limit is below the
  -- group count (`group_admit`'s and `walk_ctx`'s), not a typing claim's (`group_count()`) nor
  -- an assumed one.

def rc_validates_group := aiur_fn⟦
  fn rc_validates_group(rc: RoleCtx) -> Field {
      match (*(rc)) {
        RoleCtxNode::Mk(_, limit, _) => {
          UInt32::less_than_fields(limit, KernelRoleSpec::group_count()) } ,
        RoleCtxNode::Assumed(_, _) => {  0 } ,
      }
    }
⟧

def role_ctx_binding := aiur_fn⟦
  fn role_ctx_binding(rc: RoleCtx) -> Bytes::AddressRef {
      match (*(role_ctx_table(rc))) {
        RoleTableNode::Mk(binding, _, _, _) => {  binding } ,
      }
    }
⟧

def role_bound_addr_or_zero := aiur_fn⟦
  fn role_bound_addr_or_zero(tbl: RoleTable, r: Field) -> Bytes::AddressRef {
      match (*(tbl)) {
        RoleTableNode::Mk(_, by_role, _, _) => {
          role_map_lookup_or_default(r, by_role, (&([UInt8::BYTE_0; 32]))) } ,
      }
    }
⟧

def role_is_bound := aiur_fn⟦
  fn role_is_bound(tbl: RoleTable, r: Field) -> Field {
      let a = role_bound_addr_or_zero(tbl, r);
      match RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0) - (r + 1) {
        0 => {  1 } ,
        _ => {  0 } ,
      }
    }
⟧

def role_bound_addr := aiur_fn⟦
  fn role_bound_addr(tbl: RoleTable, r: Field) -> Bytes::AddressRef {
      assert_eq!(role_is_bound(tbl, r), 1,
        "role table does not bind a role the claim needs");
      role_bound_addr_or_zero(tbl, r)
    }
⟧

def role_addr_index := aiur_fn⟦
  fn role_addr_index(tbl: RoleTable) -> RBTreeMap::RBTreeMap<Field> {
      match (*(tbl)) {
        RoleTableNode::Mk(_, _, by_addr, _) => {  by_addr } ,
      }
    }
⟧

def role_of := aiur_fn⟦
  fn role_of(rc: RoleCtx, a: Bytes::AddressRef) -> Field {
      match (*(rc)) {
        RoleCtxNode::Mk(tbl, limit, _) => {
          let r1 = RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0);
          match r1 {
            0 => {  0 } ,
            _ => {
              match UInt32::less_than_fields(KernelRoleSpec::role_group(r1 - 1), limit) {
                1 => {
                  group_admit(tbl, KernelRoleSpec::role_group(r1 - 1));
                  r1 } ,
                _ => {  0 } ,
              } } ,
          } } ,
        RoleCtxNode::Assumed(tbl, _) => {
          RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0) } ,
      }
    }
⟧

def role_index_of := aiur_fn⟦
  fn role_index_of(rc: RoleCtx, a: Bytes::AddressRef) -> Field {
      RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(role_ctx_table(rc)), 0)
    }
⟧

def role_is_inert := aiur_fn⟦
  fn role_is_inert(rc: RoleCtx, a: Bytes::AddressRef) -> Field {
      -- 1 when the binding binds `a` to an inert role (specification kind 4: `sorryAx` and
      -- Lean's compiler-trust axioms), 0 otherwise.
      let r1 = role_index_of(rc, a);
      match r1 {
        0 => {  0 } ,
        _ => {
          match KernelRoleSpec::role_spec_kind(r1 - 1) - 4 {
            0 => {  1 } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def role_is := aiur_fn⟦
  fn role_is(rc: RoleCtx, a: Bytes::AddressRef, r: Field) -> Field {
      match role_index_of(rc, a) - (r + 1) {
        0 => {
          match role_of(rc, a) {
            0 => {  0 } ,
            _ => {  1 } ,
          } } ,
        _ => {  0 } ,
      }
    }
⟧

def role_addr := aiur_fn⟦
  fn role_addr(rc: RoleCtx, r: Field) -> Bytes::AddressRef {
      match (*(rc)) {
        RoleCtxNode::Mk(tbl, limit, _) => {
          assert_eq!(UInt32::less_than_fields(KernelRoleSpec::role_group(r), limit), 1,
            "a role is used before its group is admitted");
          let a = role_bound_addr(tbl, r);
          group_admit(tbl, KernelRoleSpec::role_group(r));
          a } ,
        RoleCtxNode::Assumed(tbl, _) => {  role_bound_addr(tbl, r) } ,
      }
    }
⟧

def role_used_implicitly := aiur_fn⟦
  fn role_used_implicitly(rc: RoleCtx, r: Field) -> Bytes::AddressRef {
      let a = role_addr(rc, r);
      KernelClaim::run_check_transitive(rc, a);
      a
    }
⟧

def group_admit := aiur_fn⟦
  fn group_admit(tbl: RoleTable, g: Field) -> () {
      group_admit_needs(tbl, KernelRoleSpec::group_needs(g));
      let rc = (&(RoleCtxNode::Mk(tbl, group_validation_limit(g), RBTreeMap::RBTreeMap::Nil)));
      validate_group_roles(rc, tbl, KernelRoleSpec::group_roles(g))
    }
⟧

def group_validation_limit := aiur_fn⟦
  fn group_validation_limit(g: Field) -> Field {
      let first_wf = KernelRoleSpec::first_well_founded_group();
      match UInt32::less_than_fields(g, first_wf) {
        1 => {  g } ,
        _ => {
          let first_literal = KernelRoleSpec::first_literal_group();
          match UInt32::less_than_fields(g, first_literal) {
            1 => {  first_wf } ,
            _ => {
              let first_equation = KernelRoleSpec::first_equation_group();
              match UInt32::less_than_fields(g, first_equation) {
                1 => {  first_literal } ,
                _ => {  first_equation } ,
              } } ,
          } } ,
      }
    }
⟧

def role_admission_checks := aiur_fn⟦
  fn role_admission_checks(r: Field) -> Field {
      match KernelRoleSpec::role_spec_kind(r) {
        0 => {
          match KernelRoleSpec::role_member_kind(r) {
            0 => {  1 } ,
            1 => {  1 } ,
            2 => {  1 } ,
            _ => {  0 } ,
          } } ,
        2 => {  1 } ,
        5 => {  1 } ,
        _ => {  0 } ,
      }
    }
⟧

def addr_quot_bound := aiur_fn⟦
  fn addr_quot_bound(rc: RoleCtx, a: Bytes::AddressRef) -> Field {
      let r1 = role_index_of(rc, a);
      match r1 {
        0 => {  0 } ,
        _ => {
          match (r1 - 1) - KernelRoleSpec::role_quot() {
            0 => {  1 } ,
            1 => {  1 } ,
            2 => {  1 } ,
            3 => {  1 } ,
            4 => {  1 } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def addr_walked_role := aiur_fn⟦
  fn addr_walked_role(rc: RoleCtx, a: Bytes::AddressRef) -> Field {
      let r1 = role_index_of(rc, a);
      match r1 {
        0 => {  0 } ,
        _ => {  role_admission_checks(r1 - 1) } ,
      }
    }
⟧

def walk_ctx := aiur_fn⟦
  fn walk_ctx(rc: RoleCtx, a: Bytes::AddressRef) -> RoleCtx {
      match (*(rc)) {
        RoleCtxNode::Mk(tbl, limit, _) => {
          let r1 = RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0);
          match r1 {
            0 => {  rc } ,
            _ => {
              let g = KernelRoleSpec::role_group(r1 - 1);
              assert_op_reached_in_order(r1 - 1, g, limit);
              match UInt32::less_than_fields(g, limit) * role_admission_checks(r1 - 1) {
                0 => {  rc } ,
                _ => {  (&(RoleCtxNode::Mk(tbl, group_validation_limit(g), RBTreeMap::RBTreeMap::Nil))) } ,
              } } ,
          } } ,
        RoleCtxNode::Assumed(_, _) => {  rc } ,
      }
    }
⟧

  -- A validation below the well-founded block never reaches an operation whose group is not
  -- below its limit: every group there needs only earlier operations, so such a reference is
  -- out of order (an operation's own record reached through a reference included). Inside
  -- the block every group is validated at one limit, so the context does not say which group
  -- is validated; there `op_order_scan` makes the check against the group's needs.

def assert_op_reached_in_order := aiur_fn⟦
  fn assert_op_reached_in_order(r: Field, g: Field, limit: Field) -> () {
      match KernelRoleSpec::role_spec_kind(r) {
        2 => {
          match UInt32::less_than_fields(limit, KernelRoleSpec::first_well_founded_group()) {
            1 => {
              assert_eq!(UInt32::less_than_fields(g, limit), 1,
                "an operation is reached before its group is validated");
              () } ,
            _ => {  () } ,
          } } ,
        _ => {  () } ,
      }
    }
⟧

  -- The walk's order assertion (`walk_ctx`) at a record a family check reaches through its
  -- payload, where no `walk_ctx` passes: an advice record, a witnessed reference, a used
  -- reference of an advice, container or family record. Below the well-founded block such a
  -- record bound to an operation must be in force; inside the block `op_order_scan` refuses
  -- the modeled block itself, so no payload is checked there; an assumed binding asserts
  -- nothing, as in `walk_ctx`.

def assert_in_order := aiur_fn⟦
  fn assert_in_order(rc: RoleCtx, a: Bytes::AddressRef) -> () {
      match (*(rc)) {
        RoleCtxNode::Mk(tbl, limit, _) => {
          let r1 = RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0);
          match r1 {
            0 => {  () } ,
            _ => {  assert_op_reached_in_order(r1 - 1, KernelRoleSpec::role_group(r1 - 1), limit) } ,
          } } ,
        RoleCtxNode::Assumed(_, _) => {  () } ,
      }
    }
⟧

  -- Inside the well-founded block: what `a` references, up to the records at which the scan
  -- stops, reaches an operation only if that operation's group is below `limit` or among
  -- `needs`, the needs of the group being validated. A referenced operation is not entered: its
  -- own validation scanned its closure. The scan stops at a role-bound record in force that is
  -- no operation, unless the role is an anchor whose validation does not walk its record
  -- (`anchor_walked` answers 0): the record of a walked role, of a walked anchor and what a
  -- standard axiom's record references were walked in their own group, below the block, where
  -- every reference to an operation is to one in force; the quotient package is bound at
  -- committed records; no walk passes an inert axiom. An anchor no validation walks has had no
  -- such walk, and the walk of this validation does not stop at it, so the scan goes on into
  -- what its record references.

def op_order_scan := aiur_fn⟦
  fn op_order_scan(tbl: RoleTable, limit: Field, needs: Lists::List<Field>, a: Bytes::AddressRef) -> () {
      let r1 = RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0);
      match r1 {
        0 => {  op_order_scan_refs(tbl, limit, needs, a) } ,
        _ => {
          let r = r1 - 1;
          let in_force = UInt32::less_than_fields(KernelRoleSpec::role_group(r), limit);
          match KernelRoleSpec::role_spec_kind(r) {
            2 => {
              let ok = match in_force {
                1 => {  1 } ,
                _ => {  KernelClaim::g_list_has(needs, r) } ,
              };
              assert_eq!(ok, 1, "an operation reaches an operation its group does not need");
              () } ,
            1 => {
              match in_force * anchor_walked(r) {
                1 => {  () } ,
                _ => {  op_order_scan_refs(tbl, limit, needs, a) } ,
              } } ,
            _ => {
              match in_force {
                1 => {  () } ,
                _ => {  op_order_scan_refs(tbl, limit, needs, a) } ,
              } } ,
          } } ,
      }
    }
⟧

  -- The references of `a`'s record, as the walk follows them: a projection's block, and every
  -- reference the record uses (`KernelClaim::const_idxs_of`).

def op_order_scan_refs := aiur_fn⟦
  fn op_order_scan_refs(tbl: RoleTable, limit: Field, needs: Lists::List<Field>, a: Bytes::AddressRef) -> () {
      let c = Ingress::load_verified_constant(a);
      match c {
        Ixon::Constant::Mk(info, _, refs, _, _) => {
          match info {
            Ixon::ConstantInfo::IPrj(p) => {
              match p { Ixon::InductiveProj::Mk(_, b) => {  op_order_scan(tbl, limit, needs, b) } , } } ,
            Ixon::ConstantInfo::CPrj(p) => {
              match p { Ixon::ConstructorProj::Mk(_, _, b) => {  op_order_scan(tbl, limit, needs, b) } , } } ,
            Ixon::ConstantInfo::RPrj(p) => {
              match p { Ixon::RecursorProj::Mk(_, b) => {  op_order_scan(tbl, limit, needs, b) } , } } ,
            Ixon::ConstantInfo::DPrj(p) => {
              match p { Ixon::DefinitionProj::Mk(_, b) => {  op_order_scan(tbl, limit, needs, b) } , } } ,
            Ixon::ConstantInfo::Muts(_) => {
              -- no mutual or nested block inside the well-founded block: its payload (family
              -- record, advice, witnessed references) would be checked in an operation's group
              -- with no order against the operations
              assert_eq!(KernelModeled::block_is_modeled(a), 0,
                "an operation reaches a mutual or nested family");
              () } ,
            _ => {  () } ,
          };
          op_order_scan_list(tbl, limit, needs, refs, KernelClaim::const_idxs_of(c), 0) } ,
      }
    }
⟧

def op_group_needs := aiur_fn⟦
  fn op_group_needs(r: Field) -> Lists::List<Field> {
      KernelRoleSpec::group_needs(KernelRoleSpec::role_group(r))
    }
⟧

def op_order_scan_list := aiur_fn⟦
  fn op_order_scan_list(tbl: RoleTable, limit: Field, needs: Lists::List<Field>,
                        refs: Lists::List<Bytes::AddressRef>, used: Lists::List<Field>, i: Field) -> () {
      match (*(refs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(b, rest) => {
          match KernelClaim::g_list_has(used, i) {
            1 => {  op_order_scan(tbl, limit, needs, b) } ,
            _ => {  () } ,
          };
          op_order_scan_list(tbl, limit, needs, rest, used, i + 1) } ,
      }
    }
⟧

def walk_covered := aiur_fn⟦
  fn walk_covered(rc: RoleCtx, a: Bytes::AddressRef) -> Field {
      match (*(rc)) {
        RoleCtxNode::Mk(_, _, _) => {  0 } ,
        RoleCtxNode::Assumed(tbl, _) => {
          let r1 = RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0);
          match r1 {
            0 => {  0 } ,
            _ => {  role_admission_checks(r1 - 1) } ,
          } } ,
      }
    }
⟧

def validate_binding := aiur_fn⟦
  fn validate_binding(binding: Bytes::AddressRef) -> () {
      let tbl = load_role_table(binding);
      assert_all_roles_bound(tbl, 0);
      admit_all_groups(tbl, 0)
    }
⟧

def assert_all_roles_bound := aiur_fn⟦
  fn assert_all_roles_bound(tbl: RoleTable, r: Field) -> () {
      match r - KernelRoleSpec::role_count() {
        0 => {  () } ,
        _ => {
          assert_eq!(role_is_bound(tbl, r), 1, "binding claim: a role is unbound");
          assert_all_roles_bound(tbl, r + 1) } ,
      }
    }
⟧

def admit_all_groups := aiur_fn⟦
  fn admit_all_groups(tbl: RoleTable, g: Field) -> () {
      match g - KernelRoleSpec::group_count() {
        0 => {  () } ,
        _ => {
          group_admit(tbl, g);
          admit_all_groups(tbl, g + 1) } ,
      }
    }
⟧

def group_admit_needs := aiur_fn⟦
  fn group_admit_needs(tbl: RoleTable, needs: Lists::List<Field>) -> () {
      match (*(needs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(r, rest) => {
          group_admit(tbl, KernelRoleSpec::role_group(r));
          group_admit_needs(tbl, rest) } ,
      }
    }
⟧

def validate_group_roles := aiur_fn⟦
  fn validate_group_roles(rc: RoleCtx, tbl: RoleTable, rs: Lists::List<Field>) -> () {
      match (*(rs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(r, rest) => {
          validate_role(rc, tbl, r);
          validate_group_roles(rc, tbl, rest) } ,
      }
    }
⟧

def validate_role := aiur_fn⟦
  fn validate_role(rc: RoleCtx, tbl: RoleTable, r: Field) -> () {
      let a = role_bound_addr(tbl, r);
      let ci = (*(Ingress::get_ci(a)));
      assert_eq!(KernelInfer::const_num_lvls(ci), KernelRoleSpec::role_levels(r),
        "a bound role has the wrong number of universe parameters");
      match KernelRoleSpec::role_spec_kind(r) {
        0 => {  validate_member(rc, tbl, r, a, ci) } ,
        1 => {  validate_anchor(rc, tbl, r, ci) } ,
        2 => {  validate_op(rc, tbl, r, a, ci) } ,
        3 => {  validate_standard_axiom(rc, tbl, r, ci) } ,
        4 => {  validate_inert_axiom(rc, tbl, r, ci) } ,
        5 => {  validate_eqns(rc, tbl, r, a, ci) } ,
      }
    }
⟧

def assert_type_meets := aiur_fn⟦
  fn assert_type_meets(rc: RoleCtx, ty: KernelTypes::KExpr, spec: KernelTypes::KExpr) -> () {
      assert_eq!(KernelDefEq::k_is_def_eq(rc, ty, spec, (&(Lists::Node::Nil))), 1,
            "a bound role's type does not meet its specification");
          ()
    }
⟧

def assert_type_pinned := aiur_fn⟦
  fn assert_type_pinned(ty: KernelTypes::KExpr, spec: KernelTypes::KExpr) -> () {
      assert_eq!(KernelCheck::kexpr_struct_eq(ty, spec), 1,
            "a bound role's type does not meet its specification");
          ()
    }
⟧

def assert_safe_role := aiur_fn⟦
  fn assert_safe_role(ci: KernelTypes::KConstantInfo) -> () {
      assert_eq!(KernelCheck::is_unsafe_ci(ci), 0, "a bound role is unsafe");
      ()
    }
⟧

def validate_member := aiur_fn⟦
  fn validate_member(rc: RoleCtx, tbl: RoleTable, r: Field, a: Bytes::AddressRef,
        ci: KernelTypes::KConstantInfo) -> () {
      assert_safe_role(ci);
      -- the member's type is closed over its levels, as the anchors' and axioms' validators
      -- check it, before it is compared with the pinned type
      KernelCheck::validate_expr_well_scoped(KernelInfer::const_type_of(ci), 0,
        KernelInfer::const_num_lvls(ci));
      assert_type_pinned(KernelInfer::const_type_of(ci), KernelRoleSpec::role_type(tbl, r));
      match KernelRoleSpec::role_member_kind(r) {
        0 => {
          match ci {
            KernelTypes::KConstantInfo::Induct(_, _, _, _, nctors, _, _, _) => {
              assert_eq!(nctors, KernelRoleSpec::role_ctor_count(r),
                "a bound inductive has the wrong number of constructors");
              KernelClaim::run_check_transitive(rc, a) } ,
          } } ,
        1 => {
          match ci {
            KernelTypes::KConstantInfo::Ctor(_, _, block, ind_idx, cidx, nparams, nfields, _) => {
              let (ind_role, want_cidx, want_params, want_fields) = KernelRoleSpec::role_ctor_of(r);
              match (*(Ingress::get_ci(role_bound_addr(tbl, ind_role)))) {
                KernelTypes::KConstantInfo::Induct(_, _, _, _, _, _, ind_block, ind_ind_idx) => {
                  assert_eq!(Bytes::address_eq(block, ind_block), 1,
                    "a bound constructor is not its inductive's");
                  assert_eq!(ind_idx, ind_ind_idx,
                    "a bound constructor is not its inductive's");
                  () } ,
              };
              assert_eq!(cidx, want_cidx, "a bound constructor has the wrong index");
              assert_eq!(nparams, want_params,
                "a bound constructor has the wrong number of parameters");
              assert_eq!(nfields, want_fields,
                "a bound constructor has the wrong number of fields");
              KernelClaim::run_check_transitive(rc, a) } ,
          } } ,
        2 => {
          match ci {
            KernelTypes::KConstantInfo::Rec(_, _, np, ni, nmot, nmin, _, _, _, _, _) => {
              -- the recursors of `Iff` and `Nonempty`: the major premise's index and the rules'
              -- prefix are the pinned ones (the level count is the pinned type's,
              -- `validate_role`)
              match r {
                25 => {
                  assert_eq!(((np + nmot) + nmin) + ni, 4,
                    "a bound recursor's major premise is not at its pinned index");
                  assert_eq!((np + nmot) + nmin, 4,
                    "a bound recursor's rules' prefix is not its pinned length");
                  () } ,
                28 => {
                  assert_eq!(((np + nmot) + nmin) + ni, 3,
                    "a bound recursor's major premise is not at its pinned index");
                  assert_eq!((np + nmot) + nmin, 3,
                    "a bound recursor's rules' prefix is not its pinned length");
                  () } ,
                _ => {  () } ,
              };
              KernelClaim::run_check_transitive(rc, a) } ,
          } } ,
        3 => {
          match ci {
            KernelTypes::KConstantInfo::Axiom(_, ty, _) => {
              KernelCheck::validate_expr_well_scoped(ty, 0, KernelRoleSpec::role_levels(r));
              KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
              () } ,
          } } ,
        4 => {  assert_quot_kind(ci, 0) } ,
        5 => {  assert_quot_kind(ci, 1) } ,
        6 => {  assert_quot_kind(ci, 2) } ,
        7 => {  assert_quot_kind(ci, 3) } ,
      }
    }
⟧

def assert_quot_kind := aiur_fn⟦
  fn assert_quot_kind(ci: KernelTypes::KConstantInfo, want: Field) -> () {
      match ci {
        KernelTypes::KConstantInfo::Quot(_, _, kind) => {
          let k = match kind {
            Ixon::QuotKind::Typ => {  0 } ,
            Ixon::QuotKind::Ctor => {  1 } ,
            Ixon::QuotKind::Lift => {  2 } ,
            Ixon::QuotKind::Ind => {  3 } ,
          };
          assert_eq!(k, want, "a bound quotient constant has the wrong kind");
          () } ,
      }
    }
⟧

  -- The literal anchors' record kinds: `List.nil`, `List.cons` (30, 31) are constructors and
  -- `String.ofList`, `Char.ofNat` (38, 40) definitions, as the kernel's literal rules read them.
  -- Any other anchor: no kind is asked.

def anchor_kind_ok := aiur_fn⟦
  fn anchor_kind_ok(r: Field, ci: KernelTypes::KConstantInfo) -> Field {
      let is_ctor = match ci {
        KernelTypes::KConstantInfo::Ctor(_, _, _, _, _, _, _, _) => {  1 } ,
        _ => {  0 } ,
      };
      let is_defn = match ci {
        KernelTypes::KConstantInfo::Defn(_, _, _, _, _) => {  1 } ,
        _ => {  0 } ,
      };
      match r {
        30 => {  is_ctor } ,
        31 => {  is_ctor } ,
        38 => {  is_defn } ,
        40 => {  is_defn } ,
        _ => {  1 } ,
      }
    }
⟧

def validate_anchor := aiur_fn⟦
  fn validate_anchor(rc: RoleCtx, tbl: RoleTable, r: Field, ci: KernelTypes::KConstantInfo) -> () {
      assert_safe_role(ci);
      assert_eq!(anchor_kind_ok(r, ci), 1, "a literal anchor is bound to a record of the wrong kind");
      let ty = KernelInfer::const_type_of(ci);
      -- the anchor's type is closed and a type, before it is compared with the role's spec
      KernelCheck::validate_expr_well_scoped(ty, 0, KernelInfer::const_num_lvls(ci));
      KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
      let spec = KernelRoleSpec::role_type(tbl, r);
      match r {
        4 => {  assert_type_pinned(ty, spec) } ,
        5 => {  assert_type_pinned(ty, spec) } ,
        6 => {  assert_type_pinned(ty, spec) } ,
        7 => {  assert_type_pinned(ty, spec) } ,
        20 => {  assert_type_pinned(ty, spec) } ,
        21 => {  assert_type_pinned(ty, spec) } ,
        22 => {  assert_type_pinned(ty, spec) } ,
        29 => {  assert_type_pinned(ty, spec) } ,
        30 => {  assert_type_pinned(ty, spec) } ,
        31 => {  assert_type_pinned(ty, spec) } ,
        37 => {  assert_type_pinned(ty, spec) } ,
        38 => {  assert_type_pinned(ty, spec) } ,
        39 => {  assert_type_pinned(ty, spec) } ,
        40 => {  assert_type_pinned(ty, spec) } ,
        _ => {  assert_type_meets(rc, ty, spec) } ,
      };
      -- the record itself, with its closure, in this group's validation context: the anchor's
      -- own role is not in force here, every role the record may use is
      match anchor_walked(r) {
        1 => {  KernelClaim::run_check_transitive(rc, role_bound_addr(tbl, r)) } ,
        _ => {  () } ,
      }
    }
⟧

  -- The anchors whose records role validation checks with their closures, each in its own
  -- group: `Bool`, `Bool.false`, `Bool.true`, `Bool.rec` (4-7), `And`, `And.intro`, `And.rec`
  -- (20-22), the literal support `List`, `List.nil`, `List.cons` (29-31), `String`,
  -- `String.ofList`, `Char`, `Char.ofNat` (37-40), and `of_decide_eq_true`,
  -- `of_decide_eq_false` (63-64).

def anchor_walked := aiur_fn⟦
  fn anchor_walked(r: Field) -> Field {
      match r {
        4 => {  1 } ,
        5 => {  1 } ,
        6 => {  1 } ,
        7 => {  1 } ,
        20 => {  1 } ,
        21 => {  1 } ,
        22 => {  1 } ,
        29 => {  1 } ,
        30 => {  1 } ,
        31 => {  1 } ,
        37 => {  1 } ,
        38 => {  1 } ,
        39 => {  1 } ,
        40 => {  1 } ,
        63 => {  1 } ,
        64 => {  1 } ,
        _ => {  0 } ,
      }
    }
⟧

def validate_standard_axiom := aiur_fn⟦
  fn validate_standard_axiom(rc: RoleCtx, tbl: RoleTable, r: Field,
        ci: KernelTypes::KConstantInfo) -> () {
      match ci {
        KernelTypes::KConstantInfo::Axiom(nlvls, ty, u) => {
          assert_eq!(u, 0, "a bound standard axiom is unsafe");
          KernelCheck::validate_expr_well_scoped(ty, 0, nlvls);
          KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
          assert_type_pinned(ty, KernelRoleSpec::role_type(tbl, r));
          -- what the bound record references is checked here, in this group's context; not
          -- the axiom itself, which is not in force in its own group (the axiom arm refuses it)
          let c = Ingress::load_verified_constant(role_bound_addr(tbl, r));
          match c {
            Ixon::Constant::Mk(_, sharing, refs, _, _) => {
              KernelClaim::assert_safe_record_refs(rc, role_bound_addr(tbl, r), c);
              match (*(sharing)) {
                Lists::Node::Nil => {  () } ,
                Lists::Node::Cons(_, _) => {
                  assert_eq!(0, 1, "a bound standard axiom carries sharing entries");
                  () } ,
              };
              KernelClaim::walk_refs_transitive(rc, refs, KernelClaim::const_idxs_of(c), 0) } ,
          } } ,
      }
    }
⟧

def validate_inert_axiom := aiur_fn⟦
  fn validate_inert_axiom(rc: RoleCtx, tbl: RoleTable, r: Field,
        ci: KernelTypes::KConstantInfo) -> () {
      match ci {
        KernelTypes::KConstantInfo::Axiom(nlvls, ty, u) => {
          assert_eq!(u, 0, "a bound inert axiom is unsafe");
          KernelCheck::validate_expr_well_scoped(ty, 0, nlvls);
          KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
          assert_type_pinned(ty, KernelRoleSpec::role_type(tbl, r)) } ,
      }
    }
⟧

def role_evidence := aiur_fn⟦
  fn role_evidence(tbl: RoleTable, r: Field) -> Lists::List<RoleEvidence> {
      match (*(tbl)) {
        RoleTableNode::Mk(_, _, _, evidence) => {
          role_map_lookup_or_default(r, evidence, (&(Lists::Node::Nil))) } ,
      }
    }
⟧

def validate_op := aiur_fn⟦
  fn validate_op(rc: RoleCtx, tbl: RoleTable, r: Field, a: Bytes::AddressRef,
        ci: KernelTypes::KConstantInfo) -> () {
      let record = Ingress::load_verified_constant(a);
      match record {
        Ixon::Constant::Mk(info, _, _, _, _) => {
          match info {
            Ixon::ConstantInfo::Defn(_) => {  () } ,
            _ => {
              assert_eq!(0, 1, "a bound operation is not a standalone definition");
              () } ,
          } } ,
      };
      match ci {
        KernelTypes::KConstantInfo::Defn(_, ty, val, safety, _) => {
          match safety {
            Ixon::DefinitionSafety::Safe => {  () } ,
            _ => {
              assert_eq!(0, 1, "a bound operation is not a safe definition");
              () } ,
          };
          assert_type_pinned(ty, KernelRoleSpec::role_type(tbl, r));
          KernelClaim::run_check_transitive(rc, a);
          -- inside the well-founded block, the operations the record reaches are in order
          match KernelRoleSpec::op_evidence_is_proof(r) {
            1 => {  op_order_scan_refs(tbl, role_ctx_limit(rc), op_group_needs(r), a) } ,
            _ => {  () } ,
          };
          let ev = role_evidence(tbl, r);
          assert_eq!(Lists::length(ev), KernelRoleSpec::op_equation_count(r),
            "an operation's evidence does not match its equations");
          validate_op_equations(rc, tbl, r, a, val, ev, 0) } ,
      }
    }
⟧

  -- An operation's equations hold for its value: each side opened under two `Nat` variables
  -- (`x` is `BVar(1)`, `y` is `BVar(0)`), with every occurrence of the operation replaced by its
  -- record's value `val` (closed), so that nothing here needs the operation stored.

def validate_op_equations := aiur_fn⟦
  fn validate_op_equations(rc: RoleCtx, tbl: RoleTable, r: Field, a: Bytes::AddressRef,
        val: KernelTypes::KExpr, ev: Lists::List<RoleEvidence>, k: Field) -> () {
      match (*(ev)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(e, rest) => {
          match KernelRoleSpec::op_evidence_is_proof(r) {
            0 => {
              match e {
                RoleEvidence::Defeq => {
                  let (lhs, types) = open_two_lams(KernelRoleSpec::op_equation_lhs(tbl, r, k));
                  let (rhs, _) = open_two_lams(KernelRoleSpec::op_equation_rhs(tbl, r, k));
                  assert_eq!(KernelDefEq::k_is_def_eq(rc, KernelSubst::subst_const(lhs, a, val),
                      KernelSubst::subst_const(rhs, a, val), types), 1,
                    "an operation's equation does not hold by definition");
                  () } ,
                RoleEvidence::Proof(_) => {
                  assert_eq!(0, 1, "a structural operation's evidence must be definitional");
                  () } ,
              } } ,
            _ => {
              match e {
                RoleEvidence::Defeq => {
                  assert_eq!(0, 1, "a well-founded operation's evidence must be proofs");
                  () } ,
                RoleEvidence::Proof(thm) => {
                  let tc = Ingress::load_verified_constant(thm);
                  match tc {
                    Ixon::Constant::Mk(info, _, _, _, _) => {
                      match info {
                        Ixon::ConstantInfo::Defn(d) => {
                          match d {
                            Ixon::Definition::Mk(kind, _, _, _, _, _) => {
                              match kind {
                                Ixon::DefKind::Theorem => { () } ,
                                _ => {
                                  assert_eq!(0, 1, "an operation certificate is not a standalone theorem");
                                  () } ,
                              } } ,
                          } } ,
                        _ => {
                          assert_eq!(0, 1, "an operation certificate is not a standalone theorem");
                          () } ,
                      } } ,
                  };
                  match (*(Ingress::get_ci(thm))) {
                    KernelTypes::KConstantInfo::Thm(nlvls, _, pval) => {
                      assert_eq!(nlvls, 0, "certificate theorem has universe parameters");
                      -- the proof with the operation replaced by its value, closed and level-free;
                      -- the theorem record itself is not walked and its type is not used
                      let p = KernelSubst::subst_const(pval, a, val);
                      KernelCheck::validate_expr_well_scoped(p, 0, 0);
                      -- what the proof names, the theorem's references but the operation, checked
                      -- with their closures; none of them reaches the operation (the order rule)
                      match tc {
                        Ixon::Constant::Mk(_, _, refs, _, _) => {
                          let used = KernelClaim::const_idxs_of(tc);
                          KernelClaim::assert_safe_refs_except(rc, refs, used, a);
                          walk_refs_except(rc, refs, used, 0, a);
                          op_order_scan_except(tbl, role_ctx_limit(rc), op_group_needs(r), refs, used, 0, a) } ,
                      };
                      -- the certificate opened: its hypotheses are the context, innermost first,
                      -- its equation the expected type at depth 2 + n, and the proof is applied to
                      -- x, y and the hypotheses' variables
                      let (eqn, types) = open_foralls(
                        KernelSubst::subst_const(KernelRoleSpec::op_certificate(tbl, r, k), a, val),
                        (&(Lists::Node::Nil)));
                      let d = Lists::length(types);
                      KernelInfer::k_check(rc, KernelWhnf::apply_spine(p, KernelModeled::bvars_desc(d, d)),
                        eqn, types) } ,
                  } } ,
              } } ,
          };
          validate_op_equations(rc, tbl, r, a, val, rest, k + 1) } ,
      }
    }
⟧

  -- A rendered certificate `∀ x y h₁ … hₙ, E`: `E`, open at depth `2 + n`, and the binders'
  -- types, innermost first.

def open_foralls := aiur_fn⟦
  fn open_foralls(e: KernelTypes::KExpr, acc: Lists::List<KernelTypes::KExpr>)
        -> (KernelTypes::KExpr, Lists::List<KernelTypes::KExpr>) {
      match (*(e)) {
        KernelTypes::KExprNode::Forall(t, body, _) => {
          open_foralls(body, (&(Lists::Node::Cons(t, acc)))) } ,
        _ => {  (e, acc) } ,
      }
    }
⟧

  -- The references `refs` (used at the indices `used`) walked as `KernelClaim::walk_refs_transitive`
  -- walks them, except `a`.

def walk_refs_except := aiur_fn⟦
  fn walk_refs_except(rc: RoleCtx, refs: Lists::List<Bytes::AddressRef>, used: Lists::List<Field>,
                      i: Field, a: Bytes::AddressRef) -> () {
      match (*(refs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(b, rest) => {
          match KernelClaim::g_list_has(used, i) * (1 - Bytes::address_eq(b, a)) {
            1 => {
              assert_ref_allowed(rc, b);
              match walk_covered(rc, b) {
                0 => {
                  KernelClaim::assert_not_block_ref(b);
                  KernelClaim::run_check_transitive(walk_ctx(rc, b), b) } ,
                _ => {  () } ,
              } } ,
            _ => {  () } ,
          };
          walk_refs_except(rc, rest, used, i + 1, a) } ,
      }
    }
⟧

  -- `op_order_scan` on the references `refs` (used at the indices `used`), except `a`.

def op_order_scan_except := aiur_fn⟦
  fn op_order_scan_except(tbl: RoleTable, limit: Field, needs: Lists::List<Field>,
                          refs: Lists::List<Bytes::AddressRef>, used: Lists::List<Field>, i: Field,
                          a: Bytes::AddressRef) -> () {
      match (*(refs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(b, rest) => {
          match KernelClaim::g_list_has(used, i) * (1 - Bytes::address_eq(b, a)) {
            1 => {  op_order_scan(tbl, limit, needs, b) } ,
            _ => {  () } ,
          };
          op_order_scan_except(tbl, limit, needs, rest, used, i + 1, a) } ,
      }
    }
⟧

  -- A rendered equation side `fun (x : Nat) (y : Nat) => body`: the body, open at depth 2, and
  -- the two binders' types, innermost first.

def open_two_lams := aiur_fn⟦
  fn open_two_lams(e: KernelTypes::KExpr) -> (KernelTypes::KExpr, Lists::List<KernelTypes::KExpr>) {
      match (*(e)) {
        KernelTypes::KExprNode::Lam(t1, inner, _) => {
          match (*(inner)) {
            KernelTypes::KExprNode::Lam(t2, body, _) => {
              (body, (&(Lists::Node::Cons(t2, (&(Lists::Node::Cons(t1, (&(Lists::Node::Nil))))))))) } ,
          } } ,
      }
    }
⟧

def walk_bound_anchor := aiur_fn⟦
  fn walk_bound_anchor(rc: RoleCtx, tbl: RoleTable, ar: Field) -> () {
      let a = role_bound_addr(tbl, ar);
      let ci = (*(Ingress::get_ci(a)));
      assert_eq!(KernelInfer::const_num_lvls(ci), KernelRoleSpec::role_levels(ar),
        "a bound anchor has another number of universe parameters");
      KernelClaim::run_check_transitive(rc, a);
      assert_type_meets(rc, KernelInfer::const_type_of(ci), KernelRoleSpec::role_type(tbl, ar))
    }
⟧

  -- Anchors whose records are checked with their closures when the first equation group
  -- that depends on them is validated (at limit 46, after the well-founded and literal blocks).

def validate_eqns_anchors := aiur_fn⟦
  fn validate_eqns_anchors(rc: RoleCtx, tbl: RoleTable, r: Field) -> () {
      match r {
        65 => {
          walk_bound_anchor(rc, tbl, 59);
          walk_bound_anchor(rc, tbl, 60);
          walk_bound_anchor(rc, tbl, 61);
          walk_bound_anchor(rc, tbl, 62) } ,
        68 => {
          walk_bound_anchor(rc, tbl, 66) } ,
        73 => {
          walk_bound_anchor(rc, tbl, 70);
          walk_bound_anchor(rc, tbl, 71);
          walk_bound_anchor(rc, tbl, 72) } ,
        85 => {
          walk_bound_anchor(rc, tbl, 83);
          walk_bound_anchor(rc, tbl, 84) } ,
        90 => {
          walk_bound_anchor(rc, tbl, 88);
          walk_bound_anchor(rc, tbl, 89) } ,
        96 => {
          walk_bound_anchor(rc, tbl, 94) } ,
        _ => {  () } ,
      }
    }
⟧

def validate_eqns := aiur_fn⟦
  fn validate_eqns(rc: RoleCtx, tbl: RoleTable, r: Field, a: Bytes::AddressRef,
        ci: KernelTypes::KConstantInfo) -> () {
      match ci {
        KernelTypes::KConstantInfo::Defn(nlvls, ty, _, safety, _) => {
          match safety {
            Ixon::DefinitionSafety::Safe => {  () } ,
            _ => {
              assert_eq!(0, 1, "a bound definition is not safe");
              () } ,
          };
          assert_eq!(nlvls, KernelRoleSpec::role_levels(r),
            "a bound definition has another number of universe parameters");
          assert_type_meets(rc, ty, KernelRoleSpec::role_type(tbl, r));
          validate_eqns_anchors(rc, tbl, r);
          KernelClaim::run_check_transitive(rc, a);
          let ev = role_evidence(tbl, r);
          assert_eq!(Lists::length(ev), KernelRoleSpec::eqns_equation_count(r),
            "a definition's evidence does not match its equations");
          validate_eqns_equations(rc, tbl, r, ev, 0) } ,
      }
    }
⟧

def validate_eqns_equations := aiur_fn⟦
  fn validate_eqns_equations(rc: RoleCtx, tbl: RoleTable, r: Field,
        ev: Lists::List<RoleEvidence>, k: Field) -> () {
      match (*(ev)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(e, rest) => {
          match e {
            RoleEvidence::Defeq => {
              assert_eq!(KernelRoleSpec::eqns_conditional(r, k), 0,
                "a conditional equation's evidence must be a proof");
              assert_eq!(KernelDefEq::k_is_def_eq(rc, KernelRoleSpec::eqns_lhs(tbl, r, k), KernelRoleSpec::eqns_rhs(tbl, r, k),
                  (&(Lists::Node::Nil))), 1,
                "a definition's equation does not hold by definition");
              () } ,
            RoleEvidence::Proof(thm) => {
              match (*(Ingress::get_ci(thm))) {
                KernelTypes::KConstantInfo::Thm(nlvls, tty, _) => {
                  assert_eq!(nlvls, KernelRoleSpec::role_levels(r),
                    "an equation's proof has another number of universe parameters");
                  KernelClaim::run_check_transitive(rc, thm);
                  assert_type_meets(rc, tty, KernelRoleSpec::eqns_statement(tbl, r, k)) } ,
              } } ,
          };
          validate_eqns_equations(rc, tbl, r, rest, k + 1) } ,
      }
    }
⟧

def axiom_standing := aiur_fn⟦
  fn axiom_standing(rc: RoleCtx, a: Bytes::AddressRef) -> Field {
      let tbl = role_ctx_table(rc);
      let r1 = RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0);
      match r1 {
        0 => {  RBTreeMap::rbtree_map_lookup_or_default(a, role_ctx_axioms(rc), 0) } ,
        _ => {
          let standing = axiom_role_standing(r1);
          match standing {
            0 => {  0 } ,
            _ => {
              match role_of(rc, a) {
                0 => {  0 } ,
                _ => {  standing } ,
              } } ,
          } } ,
      }
    }
⟧

def axiom_role_standing := aiur_fn⟦
  fn axiom_role_standing(r1: Field) -> Field {
      -- 1: a standard axiom (`propext`, `Classical.choice`, `Quot.sound`); 2: an inert one
      -- (specification kind 4: `sorryAx` and Lean's compiler-trust axioms), which may be
      -- declared but which no constant may use (`assert_ref_allowed`); 0: any other role.
      match r1 {
        0 => {  0 } ,
        _ => {
          let r = r1 - 1;
          match r - KernelRoleSpec::role_propext() {
            0 => {  1 } ,
            _ => {
              match r - KernelRoleSpec::role_choice() {
                0 => {  1 } ,
                _ => {
                  match r - KernelRoleSpec::role_quot_sound() {
                    0 => {  1 } ,
                    _ => {
                      match KernelRoleSpec::role_spec_kind(r) - 4 {
                        0 => {  2 } ,
                        _ => {  0 } ,
                      } } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def assert_ref_allowed := aiur_fn⟦
  fn assert_ref_allowed(rc: RoleCtx, a: Bytes::AddressRef) -> () {
      match axiom_standing(rc, a) {
        2 => {
          assert_eq!(0, 1, "a constant uses an inert axiom");
          () } ,
        _ => {  () } ,
      }
    }
⟧


  -- Port divergence: role-indexed maps (keys are role indices) are separate from
  -- the address-keyed `RBTreeMap::RBTreeMap`.

def role_map_lookup_or_default := aiur_fn⟦
  fn role_map_lookup_or_default<V>(key: Field, tree: RoleMap<V>, default: V) -> V {
      match tree {
        RoleMap::Nil => {  default } ,
        RoleMap::Node(_, k, v, left, right) => {
          let eq = key - k;
          match eq {
            0 => {  v } ,
            _ => {
              match UInt32::less_than_fields(key, k) {
                1 => {  role_map_lookup_or_default(key, (*(left)), default) } ,
                _ => {  role_map_lookup_or_default(key, (*(right)), default) } ,
              } } ,
          } } ,
      }
    }
⟧


  -- Port divergence: role contexts are compared by their limits, not by pointer.

def role_ctx_limit := aiur_fn⟦
  fn role_ctx_limit(rc: RoleCtx) -> Field {
      match (*(rc)) {
        RoleCtxNode::Assumed(_, _) => {  0 } ,
        RoleCtxNode::Mk(_, limit, _) => {  limit } ,
      }
    }
⟧

end

end IxVM
