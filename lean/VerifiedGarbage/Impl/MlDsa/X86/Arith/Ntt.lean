import VerifiedGarbage.Impl.MlDsa.X86.Arith.Basic
import VerifiedGarbage.Impl.MlKem.X86.Ntt

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_ntt` and `vg_mldsa_inv_ntt`

The layers are those of ML-KEM on x86 (`Impl.MlKem.X86.layerCode`), with
the butterflies of ML-DSA: a table of 256 zetas is stored in `scratch` as
`u32`s (through `edx`, from `eax = scratch`), and read through `ebp`; the
end of the polynomial, `f + 1024`, is stored in the argument slot of
`scratch`, which the loops over blocks compare their pointer with. In a
block, `esi` points at coefficient `j`, `edi` at `j + len`, and `ecx`
counts the butterflies left. The zetas are in Montgomery form (times
`2³² mod q`), so that `mred` of a coefficient times one is the coefficient
times the zeta, reduced.

* `ntt(f, scratch)` (Algorithm 41): the table of `ζ^BitRev8(m) · 2³² mod q`,
  and the layers with `len` = 128, 64, …, 1, whose zetas are consecutive
  from `m = 1` up. A butterfly computes `t = ζ · f[j + len] mod q` in `ebx`,
  and stores `f[j] - t` (`f[j] + q - t`, reduced) to `f[j + len]` and
  `f[j] + t` (reduced) to `f[j]`.
* `nttInv(f, scratch)` (Algorithm 42): the table of the negated zetas (the
  `z` of Algorithm 42) in Montgomery form, and the layers with `len` = 1,
  2, …, 128, whose zetas are consecutive from `m = 255` down. A butterfly
  stores `f[j] + f[j + len]` (reduced) to `f[j]` and
  `z · (f[j] + q - f[j + len]) mod q` to `f[j + len]`. Then every
  coefficient is multiplied by `8347681 = 256⁻¹ mod q`, in Montgomery form.

Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlDsa.X86.Arith

open VG.X86
open VG.Impl.MlKem.X86 (at_ leaf layerCode layers zUp zDown ldScratch)

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- `ζ^BitRev8(m) · 2³² mod q` for `m < 256`; the proofs check that it is
(`VG.Proof.MlDsa.X86.Arith.montZeta_eq`). -/
def montZetaTable : List Nat := [
  4193792, 25847, 5771523, 7861508, 237124, 7602457, 7504169, 466468, 1826347, 2353451, 8021166,
  6288512, 3119733, 5495562, 3111497, 2680103, 2725464, 1024112, 7300517, 3585928, 7830929,
  7260833, 2619752, 6271868, 6262231, 4520680, 6980856, 5102745, 1757237, 8360995, 4010497, 280005,
  2706023, 95776, 3077325, 3530437, 6718724, 4788269, 5842901, 3915439, 4519302, 5336701, 3574422,
  5512770, 3539968, 8079950, 2348700, 7841118, 6681150, 6736599, 3505694, 4558682, 3507263,
  6239768, 6779997, 3699596, 811944, 531354, 954230, 3881043, 3900724, 5823537, 2071892, 5582638,
  4450022, 6851714, 4702672, 5339162, 6927966, 3475950, 2176455, 6795196, 7122806, 1939314,
  4296819, 7380215, 5190273, 5223087, 4747489, 126922, 3412210, 7396998, 2147896, 2715295, 5412772,
  4686924, 7969390, 5903370, 7709315, 7151892, 8357436, 7072248, 7998430, 1349076, 1852771,
  6949987, 5037034, 264944, 508951, 3097992, 44288, 7280319, 904516, 3958618, 4656075, 8371839,
  1653064, 5130689, 2389356, 8169440, 759969, 7063561, 189548, 4827145, 3159746, 6529015, 5971092,
  8202977, 1315589, 1341330, 1285669, 6795489, 7567685, 6940675, 5361315, 4499357, 4751448,
  3839961, 2091667, 3407706, 2316500, 3817976, 5037939, 2244091, 5933984, 4817955, 266997, 2434439,
  7144689, 3513181, 4860065, 4621053, 7183191, 5187039, 900702, 1859098, 909542, 819034, 495491,
  6767243, 8337157, 7857917, 7725090, 5257975, 2031748, 3207046, 4823422, 7855319, 7611795,
  4784579, 342297, 286988, 5942594, 4108315, 3437287, 5038140, 1735879, 203044, 2842341, 2691481,
  5790267, 1265009, 4055324, 1247620, 2486353, 1595974, 4613401, 1250494, 2635921, 4832145,
  5386378, 1869119, 1903435, 7329447, 7047359, 1237275, 5062207, 6950192, 7929317, 1312455,
  3306115, 6417775, 7100756, 1917081, 5834105, 7005614, 1500165, 777191, 2235880, 3406031, 7838005,
  5548557, 6709241, 6533464, 5796124, 4656147, 594136, 4603424, 6366809, 2432395, 2454455, 8215696,
  1957272, 3369112, 185531, 7173032, 5196991, 162844, 1616392, 3014001, 810149, 1652634, 4686184,
  6581310, 5341501, 3523897, 3866901, 269760, 2213111, 7404533, 1717735, 472078, 7953734, 1723600,
  6577327, 1910376, 6712985, 7276084, 8119771, 4546524, 5441381, 6144432, 7959518, 6094090, 183443,
  7403526, 1612842, 4834730, 7826001, 3919660, 8332111, 7018208, 3937738, 1400424, 7534263, 1976782]

/-- `-ζ^BitRev8(m) · 2³² mod q` for `m < 256`; the proofs check that it is
(`VG.Proof.MlDsa.X86.Arith.montNegZeta_eq`). -/
def montNegZetaTable : List Nat := [
  4186625, 8354570, 2608894, 518909, 8143293, 777960, 876248, 7913949, 6554070, 6026966, 359251,
  2091905, 5260684, 2884855, 5268920, 5700314, 5654953, 7356305, 1079900, 4794489, 549488, 1119584,
  5760665, 2108549, 2118186, 3859737, 1399561, 3277672, 6623180, 19422, 4369920, 8100412, 5674394,
  8284641, 5303092, 4849980, 1661693, 3592148, 2537516, 4464978, 3861115, 3043716, 4805995,
  2867647, 4840449, 300467, 6031717, 539299, 1699267, 1643818, 4874723, 3821735, 4873154, 2140649,
  1600420, 4680821, 7568473, 7849063, 7426187, 4499374, 4479693, 2556880, 6308525, 2797779,
  3930395, 1528703, 3677745, 3041255, 1452451, 4904467, 6203962, 1585221, 1257611, 6441103,
  4083598, 1000202, 3190144, 3157330, 3632928, 8253495, 4968207, 983419, 6232521, 5665122, 2967645,
  3693493, 411027, 2477047, 671102, 1228525, 22981, 1308169, 381987, 7031341, 6527646, 1430430,
  3343383, 8115473, 7871466, 5282425, 8336129, 1100098, 7475901, 4421799, 3724342, 8578, 6727353,
  3249728, 5991061, 210977, 7620448, 1316856, 8190869, 3553272, 5220671, 1851402, 2409325, 177440,
  7064828, 7039087, 7094748, 1584928, 812732, 1439742, 3019102, 3881060, 3628969, 4540456, 6288750,
  4972711, 6063917, 4562441, 3342478, 6136326, 2446433, 3562462, 8113420, 5945978, 1235728,
  4867236, 3520352, 3759364, 1197226, 3193378, 7479715, 6521319, 7470875, 7561383, 7884926,
  1613174, 43260, 522500, 655327, 3122442, 6348669, 5173371, 3556995, 525098, 768622, 3595838,
  8038120, 8093429, 2437823, 4272102, 4943130, 3342277, 6644538, 8177373, 5538076, 5688936,
  2590150, 7115408, 4325093, 7132797, 5894064, 6784443, 3767016, 7129923, 5744496, 3548272,
  2994039, 6511298, 6476982, 1050970, 1333058, 7143142, 3318210, 1430225, 451100, 7067962, 5074302,
  1962642, 1279661, 6463336, 2546312, 1374803, 6880252, 7603226, 6144537, 4974386, 542412, 2831860,
  1671176, 1846953, 2584293, 3724270, 7786281, 3776993, 2013608, 5948022, 5925962, 164721, 6423145,
  5011305, 8194886, 1207385, 3183426, 8217573, 6764025, 5366416, 7570268, 6727783, 3694233,
  1799107, 3038916, 4856520, 4513516, 8110657, 6167306, 975884, 6662682, 7908339, 426683, 6656817,
  1803090, 6470041, 1667432, 1104333, 260646, 3833893, 2939036, 2235985, 420899, 2286327, 8196974,
  976891, 6767575, 3545687, 554416, 4460757, 48306, 1362209, 4442679, 6979993, 846154, 6403635]

/-- `8347681 · 2³² mod q`: `256⁻¹` in Montgomery form. -/
def scaleImm : BitVec 32 := 16382

/-- The 256 entries of `T` as `u32`s at `[eax]`, through `edx`. -/
def table (T : List Nat) : List Instr :=
  (List.range 256).flatMap fun k => [.mov .edx (.imm (BitVec.ofNat 32 (T.getD k 0))), .store (at_ .eax (4 * k)) .edx]

/-- The butterfly of `NTT` on `[esi]` and `[edi]` with the zeta at `[ebp]`. -/
def bflyBody : List Instr :=
  [.mov .eax (.mem (at_ .edi 0)), .mov .edx (.mem (at_ .ebp 0)), .mul .edx] +++ mred .ebx +++
  [.mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.imm qImm), .alu .sub .eax (.reg .ebx)] +++
  csubQ .eax .edx +++
  [.store (at_ .edi 0) .eax, .mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.reg .ebx)] +++
  csubQ .eax .edx +++
  [.store (at_ .esi 0) .eax, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4), .alu .sub .ecx (.imm 1)]

/-- The butterfly of `NTT⁻¹` on `[esi]` and `[edi]` with the zeta at `[ebp]`. -/
def ibflyBody : List Instr :=
  [.mov .ebx (.mem (at_ .esi 0)), .alu .add .ebx (.imm qImm), .alu .sub .ebx (.mem (at_ .edi 0)),
    .mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.mem (at_ .edi 0))] +++ csubQ .eax .edx +++
  [.store (at_ .esi 0) .eax, .mov .eax (.reg .ebx), .mov .edx (.mem (at_ .ebp 0)), .mul .edx] +++
  mred .ebx +++
  [.store (at_ .edi 0) .ebx, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4), .alu .sub .ecx (.imm 1)]

/-- The table `T`, `ebp` at entry `z`, and `f + 1024` in the slot of `scratch`. -/
def nttSetup (T : List Nat) (z : Nat) : List Instr :=
  table T +++
  [.mov .ebp (.reg .eax), .alu .add .ebp (.imm (BitVec.ofNat 32 (4 * z))), .mov .edx (.mem (at_ .esp 20)),
    .alu .add .edx (.imm 1024), .store (at_ .esp 24) .edx]

def ntt : Prog isa :=
  leaf (.seq (.block ldScratch) (.seq (.block (nttSetup montZetaTable 1))
    (layers (layerCode bflyBody zUp) [128, 64, 32, 16, 8, 4, 2, 1])))

/-- `[esi] ← [esi] · 8347681 mod q`, and on to the next coefficient. -/
def scaleBody : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .mov .edx (.imm scaleImm), .mul .edx] +++ mred .ebx +++
  [.store (at_ .esi 0) .ebx, .alu .add .esi (.imm 4), .alu .sub .ecx (.imm 1)]

def nttInv : Prog isa :=
  leaf (.seq (.block ldScratch) (.seq (.block (nttSetup montNegZetaTable 255))
    (.seq (layers (layerCode ibflyBody zDown) [1, 2, 4, 8, 16, 32, 64, 128])
      (.seq (.block [.mov .esi (.mem (at_ .esp 20))])
        (.seq (.block [.mov .ecx (.imm 256)]) (.loop (.block scaleBody) .ne))))))

end VG.Impl.MlDsa.X86.Arith
