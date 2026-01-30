import Ix.Aiur.Meta

namespace IxVM

def poseidon2 := ⟦
  fn poseidon2_permute(state: [G; 16]) -> [G; 16] {
    let state = external_linear_layer(state);

    -- First half full rounds
    let round_constants = [
      [
        0x15ebea3fc73397c3,
        0xd73cd9fbfe8e275c,
        0x8c096bfce77f6c26,
        0x4e128f68b53d8fea,
        0x29b779a36b2763f6,
        0xfe2adc6fb65acd08,
        0x8d2520e725ad0955,
        0x1c2392b214624d2a,
        0x37482118206dcc6e,
        0x2f829bed19be019a,
        0x2fe298cb6f8159b0,
        0x2bbad982deccdbbf,
        0xbad568b8cc60a81e,
        0xb86a814265baad10,
        0xbec2005513b3acb3,
        0x6bf89b59a07c2a94
      ],
      [
        0xa25deeb835e230f5,
        0x3c5bad8512b8b12a,
        0x7230f73c3cb7a4f2,
        0xa70c87f095c74d0f,
        0x6b7606b830bb2e80,
        0x6cd467cfc4f24274,
        0xfeed794df42a9b0a,
        0x8cf7cf6163b7dbd3,
        0x9a6e9dda597175a0,
        0xaa52295a684faf7b,
        0x017b811cc3589d8d,
        0x55bfb699b6181648,
        0xc2ccaf71501c2421,
        0x1707950327596402,
        0xdd2fcdcd42a8229f,
        0x8b9d7d5b27778a21
      ],
      [
        0xac9a05525f9cf512,
        0x2ba125c58627b5e8,
        0xc74e91250a8147a5,
        0xa3e64b640d5bb384,
        0xf53047d18d1f9292,
        0xbaaeddacae3a6374,
        0xf2d0914a808b3db1,
        0x18af1a3742bfa3b0,
        0x9a621ef50c55bdb8,
        0xc615f4d1cc5466f3,
        0xb7fbac19a35cf793,
        0xd2b1a15ba517e46d,
        0x4a290c4d7fd26f6f,
        0x4f0cf1bb1770c4c4,
        0x548345386cd377f5,
        0x33978d2789fddd42
      ],
      [
        0xab78c59deb77e211,
        0xc485b2a933d2be7f,
        0xbde3792c00c03c53,
        0xab4cefe8f893d247,
        0xc5c0e752eab7f85f,
        0xdbf5a76f893bafea,
        0xa91f6003e3d984de,
        0x099539077f311e87,
        0x097ec52232f9559e,
        0x53641bdf8991e48c,
        0x2afe9711d5ed9d7c,
        0xa7b13d3661b5d117,
        0x5a0e243fe7af6556,
        0x1076fae8932d5f00,
        0x9b53a83d434934e3,
        0xed3fd595a3c0344a
      ]
    ];
    let state = fold(0 .. 4, state, |state, @r|
      -- Add constants + S-box on all elements
      let state = fold(0 .. 16, state, |state, @i|
        let x = state[@i] + round_constants[@r][@i];
        let x2 = x * x;
        let x4 = x2 * x2;
        set(state, @i, x4 * x2 * x)
      );
      external_linear_layer(state)
    );

    -- Partial rounds
    let round_constants = [
      0x28eff4b01103d100,
      0x60400ca3e2685a45,
      0x1c8636beb3389b84,
      0xac1332b60e13eff0,
      0x2adafcc364e20f87,
      0x79ffc2b14054ea0b,
      0x3f98e4c0908f0a05,
      0xcdb230bc4e8a06c4,
      0x1bcaf7705b152a74,
      0xd9bca249a82a7470,
      0x91e24af19bf82551,
      0xa62b43ba5cb78858,
      0xb4898117472e797f,
      0xb3228bca606cdaa0,
      0x844461051bca39c9,
      0xf3411581f6617d68,
      0xf7fd50646782b533,
      0x6ca664253c18fb48,
      0x2d2fcdec0886a08f,
      0x29da00dd799b575e,
      0x47d966cc3b6e1e93,
      0xde884e9a17ced59e
    ];
    let state = fold(0 .. 22, state, |state, @r|
      -- Constant + S-box only on first element
      let x = state[0] + round_constants[@r];
      let x2 = x * x;
      let x4 = x2 * x2;
      let state = set(state, 0, x4 * x2 * x);
      internal_linear_layer(state)
    );

    -- Final full rounds
    let round_constants = [
      [
        0xdacf46dc1c31a045,
        0x5d2e3c121eb387f2,
        0x51f8b0658b124499,
        0x1e7dbd1daa72167d,
        0x8275015a25c55b88,
        0xe8521c24ac7a70b3,
        0x6521d121c40b3f67,
        0xac12de797de135b0,
        0xafa28ead79f6ed6a,
        0x685174a7a8d26f0b,
        0xeff92a08d35d9874,
        0x3058734b76dd123a,
        0xfa55dcfba429f79c,
        0x559294d4324c7728,
        0x7a770f53012dc178,
        0xedd8f7c408f3883b
      ],
      [
        0x39b533cf8d795fa5,
        0x160ef9de243a8c0a,
        0x431d52da6215fe3f,
        0x54c51a2a2ef6d528,
        0x9b13892b46ff9d16,
        0x263c46fcee210289,
        0xb738c96d25aabdc4,
        0x5c33a5203996d38f,
        0x2626496e7c98d8dd,
        0xc669e0a52785903a,
        0xaecde726c8ae1f47,
        0x039343ef3a81e999,
        0x2615ceaf044a54f9,
        0x7e41e834662b66e1,
        0x4ca5fd4895335783,
        0x64b334d02916f2b0
      ],
      [
        0x87268837389a6981,
        0x034b75bcb20a6274,
        0x58e658296cc2cd6e,
        0xe2d0f759acc31df4,
        0x81a652e435093e20,
        0x0b72b6e0172eaf47,
        0x4aec43cec577d66d,
        0xde78365b028a84e6,
        0x444e19569adc0ee4,
        0x942b2451fa40d1da,
        0xe24506623ea5bd6c,
        0x082854bf2ef7c743,
        0x69dbbc566f59d62e,
        0x248c38d02a7b5cb2,
        0x4f4e8f8c09d15edb,
        0xd96682f188d310cf
      ],
      [
        0x6f9a25d56818b54c,
        0xb6cefed606546cd9,
        0x5bc07523da38a67b,
        0x7df5a3c35b8111cf,
        0xaaa2cc5d4db34bb0,
        0x9e673ff22a4653f8,
        0xbd8b278d60739c62,
        0xe10d20f6925b8815,
        0xf6c87b91dd4da2bf,
        0xfed623e2f71b6f1a,
        0xa0f02fa52a94d0d3,
        0xbb5794711b39fa16,
        0xd3b94fba9d005c7f,
        0x15a26e89fad946c9,
        0xf3cb87db8a67cf49,
        0x400d2bf56aa2a577
      ]
    ];
    fold(0 .. 4, state, |state, @r|
      let state = fold(0 .. 16, state, |state, @i|
        let x = state[@i] + round_constants[@r][@i];
        let x2 = x * x;
        let x4 = x2 * x2;
        set(state, @i, x4 * x2 * x)
      );
      external_linear_layer(state)
    )
  }

  fn external_linear_layer(state: [G; 16]) -> [G; 16] {

    let [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] = state;

    -- -------------------------
    -- Step 1: Apply M4 to block 0
    -- -------------------------

    let t0_0 = x0 + x1;
    let t1_0 = x2 + x3;
    let t2_0 = (2 * x1) + t1_0;
    let t3_0 = (2 * x3) + t0_0;
    let t4_0 = (4 * t1_0) + t3_0;
    let t5_0 = (4 * t0_0) + t2_0;
    let t6_0 = t3_0 + t5_0;
    let t7_0 = t2_0 + t4_0;

    let x0p = t6_0;
    let x1p = t5_0;
    let x2p = t7_0;
    let x3p = t4_0;

    -- -------------------------
    -- Step 2: Apply M4 to block 1
    -- -------------------------

    let t0_1 = x4 + x5;
    let t1_1 = x6 + x7;
    let t2_1 = (2 * x5) + t1_1;
    let t3_1 = (2 * x7) + t0_1;
    let t4_1 = (4 * t1_1) + t3_1;
    let t5_1 = (4 * t0_1) + t2_1;
    let t6_1 = t3_1 + t5_1;
    let t7_1 = t2_1 + t4_1;

    let x4p = t6_1;
    let x5p = t5_1;
    let x6p = t7_1;
    let x7p = t4_1;

    -- -------------------------
    -- Step 3: Apply M4 to block 2
    -- -------------------------

    let t0_2 = x8 + x9;
    let t1_2 = x10 + x11;
    let t2_2 = (2 * x9) + t1_2;
    let t3_2 = (2 * x11) + t0_2;
    let t4_2 = (4 * t1_2) + t3_2;
    let t5_2 = (4 * t0_2) + t2_2;
    let t6_2 = t3_2 + t5_2;
    let t7_2 = t2_2 + t4_2;

    let x8p  = t6_2;
    let x9p  = t5_2;
    let x10p = t7_2;
    let x11p = t4_2;

    -- -------------------------
    -- Step 4: Apply M4 to block 3
    -- -------------------------

    let t0_3 = x12 + x13;
    let t1_3 = x14 + x15;
    let t2_3 = (2 * x13) + t1_3;
    let t3_3 = (2 * x15) + t0_3;
    let t4_3 = (4 * t1_3) + t3_3;
    let t5_3 = (4 * t0_3) + t2_3;
    let t6_3 = t3_3 + t5_3;
    let t7_3 = t2_3 + t4_3;

    let x12p = t6_3;
    let x13p = t5_3;
    let x14p = t7_3;
    let x15p = t4_3;

    -- -------------------------
    -- Step 5: Apply ME: final 2t = 32 additions
    --
    -- For width=16:
    -- y[i] = 2*x'i + sum of all x' in the same "column" of blocks
    -- -------------------------

    let y0  = (2 * x0p)  + x4p + x8p + x12p;
    let y1  = (2 * x1p)  + x5p + x9p + x13p;
    let y2  = (2 * x2p)  + x6p + x10p + x14p;
    let y3  = (2 * x3p)  + x7p + x11p + x15p;

    let y4  = x0p + (2 * x4p)  + x8p + x12p;
    let y5  = x1p + (2 * x5p)  + x9p + x13p;
    let y6  = x2p + (2 * x6p)  + x10p + x14p;
    let y7  = x3p + (2 * x7p)  + x11p + x15p;

    let y8  = x0p + x4p + (2 * x8p)  + x12p;
    let y9  = x1p + x5p + (2 * x9p)  + x13p;
    let y10 = x2p + x6p + (2 * x10p) + x14p;
    let y11 = x3p + x7p + (2 * x11p) + x15p;

    let y12 = x0p + x4p + x8p + (2 * x12p);
    let y13 = x1p + x5p + x9p + (2 * x13p);
    let y14 = x2p + x6p + x10p + (2 * x14p);
    let y15 = x3p + x7p + x11p + (2 * x15p);

    [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15]
  }

  fn internal_linear_layer(state: [G; 16]) -> [G; 16] {
    let sum =
      state[0]  + state[1]  + state[2]  + state[3]  +
      state[4]  + state[5]  + state[6]  + state[7]  +
      state[8]  + state[9]  + state[10] + state[11] +
      state[12] + state[13] + state[14] + state[15];

    let diag = [
      0xde9b91a467d6afbf,
      0xc5f16b9c76a9be16,
      0x0ab0fef2d540ac54,
      0x3001d27009d05772,
      0xed23b1f906d3d9ea,
      0x5ce73743cba97053,
      0x1c3bab944af4ba23,
      0x2faa105854dbafad,
      0x53ffb3ae6d421a0f,
      0xbcda9df8884ba395,
      0xfc1273e4a31807ba,
      0xc77952573d5142bf,
      0x56683339a819b85d,
      0x328fcbd8f0ddc8ea,
      0xb5101e303fce9cb6,
      0x774487b8c40089ba
    ];

    fold(0 .. 16, [0; 16], |new_state, @i|
      set(new_state, @i, diag[@i] * state[@i] + sum)
    )
  }

  fn poseidon2(input: ByteStream) -> [G; 4] {
    -- TODO: Pack 7 bytes on a single `G` before calling `poseidon_aux`.
    -- To prevent overflows, each byte must be proven as one via lookup.
    poseidon2_aux(input, [0; 16])[0..4]
  }

  fn poseidon2_aux(input: ByteStream, state: [G; 16]) -> [G; 16] {
    match input {
      ByteStream.Nil =>
        let state = set(state, 8, state[8] + 1);
        poseidon2_permute(state),
      ByteStream.Cons(x0, tail_ptr) => match load(tail_ptr) {
        ByteStream.Nil =>
          let state = set(state, 0, state[0] + x0);
          let state = set(state, 8, state[8] + 1);
          poseidon2_permute(state),
        ByteStream.Cons(x1, tail_ptr) => match load(tail_ptr) {
          ByteStream.Nil =>
            let state = set(state, 0, state[0] + x0);
            let state = set(state, 1, state[1] + x1);
            let state = set(state, 8, state[8] + 1);
          poseidon2_permute(state),
          ByteStream.Cons(x2, tail_ptr) => match load(tail_ptr) {
            ByteStream.Nil =>
              let state = set(state, 0, state[0] + x0);
              let state = set(state, 1, state[1] + x1);
              let state = set(state, 2, state[2] + x2);
              let state = set(state, 8, state[8] + 1);
              poseidon2_permute(state),
            ByteStream.Cons(x3, tail_ptr) => match load(tail_ptr) {
              ByteStream.Nil =>
                let state = set(state, 0, state[0] + x0);
                let state = set(state, 1, state[1] + x1);
                let state = set(state, 2, state[2] + x2);
                let state = set(state, 3, state[3] + x3);
                let state = set(state, 8, state[8] + 1);
              poseidon2_permute(state),
              ByteStream.Cons(x4, tail_ptr) => match load(tail_ptr) {
                ByteStream.Nil =>
                  let state = set(state, 0, state[0] + x0);
                  let state = set(state, 1, state[1] + x1);
                  let state = set(state, 2, state[2] + x2);
                  let state = set(state, 3, state[3] + x3);
                  let state = set(state, 4, state[4] + x4);
                  let state = set(state, 8, state[8] + 1);
                poseidon2_permute(state),
                ByteStream.Cons(x5, tail_ptr) => match load(tail_ptr) {
                  ByteStream.Nil =>
                    let state = set(state, 0, state[0] + x0);
                    let state = set(state, 1, state[1] + x1);
                    let state = set(state, 2, state[2] + x2);
                    let state = set(state, 3, state[3] + x3);
                    let state = set(state, 4, state[4] + x4);
                    let state = set(state, 5, state[5] + x5);
                    let state = set(state, 8, state[8] + 1);
                    poseidon2_permute(state),
                  ByteStream.Cons(x6, tail_ptr) =>
                    let state = set(state, 0, state[0] + x0);
                    let state = set(state, 1, state[1] + x1);
                    let state = set(state, 2, state[2] + x2);
                    let state = set(state, 3, state[3] + x3);
                    let state = set(state, 4, state[4] + x4);
                    let state = set(state, 5, state[5] + x5);
                    match load(tail_ptr) {
                      ByteStream.Nil =>
                        let state = set(state, 6, state[6] + x6);
                        let state = set(state, 8, state[8] + 1);
                        poseidon2_permute(state),
                      ByteStream.Cons(x7, tail_ptr) =>
                        let state = set(state, 6, state[6] + x6);
                        let state = set(state, 7, state[7] + x7);
                        let state = poseidon2_permute(state);
                        poseidon2_aux(load(tail_ptr), state),
                    },
                },
              },
            },
          },
        },
      },
    }
  }
⟧

end IxVM
