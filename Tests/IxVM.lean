import Tests.Common
import Ix.IxVM
import Ix.Aiur.Simple
import Ix.Aiur.Compile
import Blake3

def mkBlake3HashTestCase (size : Nat) : AiurTestCase :=
  let inputBytes := Array.range size |>.map Nat.toUInt8
  let outputBytes := Blake3.hash ⟨inputBytes⟩ |>.val.data
  let input := inputBytes.map .ofUInt8
  let output := outputBytes.map .ofUInt8
  let buffer := ⟨input, .ofList [(#[0], ⟨0, size⟩)]⟩ -- key is fixed as #[0]
  ⟨`blake3_test, #[], output, buffer, buffer⟩

def blake3GFunctionInput : Array Aiur.G := #[
  208, 182, 170,  29, -- 497727184
   32, 238, 139, 163, -- 2743856672
  129,  95, 137,  36, -- 612982657
  139, 123, 192, 195, -- 3284171659
  220,   3, 246,  75, -- 1274414044
  221, 228,  14, 220, -- 3691963613
]

def blake3GFunctionOutput : Array Aiur.G := #[
   85, 211,  16, 238, -- 3994080085
  128, 183, 107,  77, -- 1298904960
  138, 133,  14, 177, -- 2970518922
   29,  87,  61, 185, -- 3107804957
]

def blake3CompressInput : Array Aiur.G := #[
  -- chaining value
  115,  16, 184, 201, -- 3384283251
   77, 162, 254, 111, -- 1878958669
  195, 185,  26, 231, -- 3877288387
  235, 137, 218, 133, -- 2245691883
  122, 192, 150, 246, -- 4137074810
  126, 234, 126,  96, -- 1618930302
   65,  41, 245, 119, -- 2012555585
  184, 184,  39,  81, -- 1361557688
  -- block words
  118, 167, 178,  10, -- 179480438
  250, 210, 157,   8, -- 144560890
  222,  39, 193,  29, -- 499197918
  200, 255,  76, 123, -- 2068643784
    1,  74,   6, 113, -- 1896237569
   46, 141,  18, 103, -- 1729269038
  121,   5, 161,  83, -- 1403061625
  183, 199, 227, 128, -- 2162411447
  211, 179, 185, 192, -- 3233395667
  179, 132, 171,  41, -- 699106483
  197, 233, 178,  39, -- 666036677
  134,  70, 139, 128, -- 2156611206
  122, 205,  14,  14, -- 235851130
  186, 141,  27,  51, -- 857443770
   44, 188,  77, 255, -- 4283284524
  134, 230,  91,  72, -- 1213982342
  -- counter
  224, 138, 26, 53, 179, 156, 136, 9, -- 686971236678011616
  -- block len
  175, 248, 200,  87, -- 1472788655
  -- flags
  145, 111,  62,  59, -- 993947537
]

def blake3CompressOutput : Array Aiur.G := #[
   89,  90, 149,  32, -- 546658905
  253, 164, 130, 149, -- 2508367101
   82, 136, 153,  80, -- 1352239186
  134, 108,  79, 255, -- 4283395206
   24, 187,  77, 106, -- 1783479064
  123, 110, 225, 217, -- 3655429755
   78,  46, 203, 131, -- 2211130958
   55, 141, 254, 224, -- 3774778679
]

def ixTestCases : List AiurTestCase := [
  -- .noIO `blake3_g_function blake3GFunctionInput blake3GFunctionOutput,
  -- .noIO `blake3_compress blake3CompressInput blake3CompressOutput,
  -- .noIO `relaxed_u64_succ #[0, 0, 0, 0, 0, 0, 0, 0] #[1, 0, 0, 0, 0, 0, 0, 0],
  -- .noIO `relaxed_u64_succ #[255, 0, 0, 0, 0, 0, 0, 0] #[0, 1, 0, 0, 0, 0, 0, 0],
  -- .noIO `relaxed_u64_succ #[255, 255, 0, 0, 0, 0, 0, 0] #[0, 0, 1, 0, 0, 0, 0, 0],
  -- .noIO `relaxed_u64_succ #[255, 255, 255, 0, 0, 0, 0, 0] #[0, 0, 0, 1, 0, 0, 0, 0],
  -- .noIO `relaxed_u64_succ #[255, 255, 255, 255, 0, 0, 0, 0] #[0, 0, 0, 0, 1, 0, 0, 0],
  -- .noIO `relaxed_u64_succ #[255, 255, 255, 255, 255, 0, 0, 0] #[0, 0, 0, 0, 0, 1, 0, 0],
  -- .noIO `relaxed_u64_succ #[255, 255, 255, 255, 255, 255, 0, 0] #[0, 0, 0, 0, 0, 0, 1, 0],
  -- .noIO `relaxed_u64_succ #[255, 255, 255, 255, 255, 255, 255, 0] #[0, 0, 0, 0, 0, 0, 0, 1],
  -- .noIO `relaxed_u64_succ #[255, 255, 255, 255, 255, 255, 255, 255] #[0, 0, 0, 0, 0, 0, 0, 0],
  mkBlake3HashTestCase 0,
  -- mkBlake3HashTestCase 32,
  -- mkBlake3HashTestCase 64,
  -- mkBlake3HashTestCase 96,
  -- mkBlake3HashTestCase 1024,
  -- mkBlake3HashTestCase 1056,
  -- mkBlake3HashTestCase 1088,
  -- mkBlake3HashTestCase 1120,
  -- mkBlake3HashTestCase 2048,
  -- mkBlake3HashTestCase 2080,
  -- mkBlake3HashTestCase 2112,
  -- mkBlake3HashTestCase 2144,
]

def Tests.IxVM.suite := [
  mkAiurTests ixVM ixTestCases
]
