import VerifiedGarbage.Impl.Aes.X86_64.Vaes
import VerifiedGarbage.Impl.Gcm.X86_64.Vpclmul

/-!
# AES-GCM's counter mode and GHASH, interleaved, with VAES and VPCLMULQDQ

`vg_aes_gcm_encrypt_blocks` for CPUs with VAES, VPCLMULQDQ and AVX2, on
groups of sixteen blocks: `(ctx = rdi, rounds = rsi, counter = rdx, y = rcx,
data = r8, n = r9, scratch = [rsp + 8])`.

`vg_ghash_vpclmul`'s setup computes `H'`–`H'¹⁶` from the hash subkey at
`ctx + 240`, which are stored, paired, to `scratch` (the pair that the `k`-th
load of a sixteen-block body multiplies at `scratch + 32 k`). The first group
is encrypted as `vg_aes_ctr32_vaes` does, sixteen blocks at a time in the
lanes of `ymm3`–`ymm6` (two batches of eight); then each group is encrypted
while the previous group's ciphertext is hashed, the products of the GHASH
of the previous group placed between the rounds of the encryption of this
one, so that the two, which are independent, share the CPU. The last
group's ciphertext is then hashed alone, with the same loads.

Registers: `ymm0` the byte-reversal mask, `ymm1` the reduction constant,
`xmm2` `Y`, `ymm3`–`ymm6` eight blocks being encrypted, `ymm7` two blocks
being hashed, `ymm8`–`ymm11` the products and a temporary, `ymm12` a pair of
powers, `ymm13` a round key, `ymm14` the counter pair and `ymm15` the counter
increment (2 in each lane). `rdx` points to the group being hashed (the one
before the group being encrypted), `rax` to the counter, `r10` to the last
round key, `r11` to `scratch`.
-/

namespace VG.Impl.Gcm.X86_64.Stitch

open VG.X86_64
open VG.Impl.Aes.X86_64.Vaes (keyOpK roundK aesK ctrsK xorDataK)
open VG.Impl.Gcm.X86_64.Pclmul (at_ revMask poly hInv mul)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16 powers powers16 zero ld reduce combine)

def aregs : List XReg := [.xmm3, .xmm4, .xmm5, .xmm6]

/-- The powers of the `k`-th load of a sixteen-block body, from `scratch`,
into `ymm12`, then that load. -/
def ghLoad (k : Nat) : List Instr := .vmovdquLoad .l256 .xmm12 (at_ .r11 (32 * k)) :: ld k .xmm12

/-- Each register of `rs` stored to `base + 32 (j + i)`. -/
def storesK (base : Reg) : List XReg → Nat → List Instr
  | [], _ => []
  | r :: rs, j => .vmovdquStore .l256 (at_ base (32 * j)) r :: storesK base rs (j + 1)

/-- The registers of the powers, in the order of the loads of a body. -/
def pregs : List XReg := [.xmm3, .xmm4, .xmm5, .xmm6, .xmm15, .xmm14, .xmm13, .xmm12]

/-- `H'`–`H'¹⁶` from the hash subkey at `ctx + 240`, as `vg_ghash_vpclmul`
computes them, in `ymm3`–`ymm6` and `ymm12`–`ymm15`. -/
def setupG : List Instr :=
  Pclmul.const .xmm0 revMask ++ Pclmul.const .xmm1 poly ++
  [.movdquLoad .xmm7 (at_ .rdi 240), .xop (.bin .pshufb .xmm7 .xmm0)] ++ hInv ++
  mul .xmm4 .xmm3 .xmm3 ++ mul .xmm5 .xmm4 .xmm3 ++ mul .xmm6 .xmm5 .xmm3 ++ powers ++ powers16

/-- `Y`, the counter pair, the increment, the last round key's address, and
the pointers of the loop. -/
def setupC : List Instr :=
  [.vmovdquLoad .l128 .xmm2 (at_ .rcx 0), .vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
   .movImm64 .rax 1, .vop (.vmovq .xmm15 .rax),
   .vmovdquLoad .l128 .xmm14 (at_ .rdx 0), .vop (.vbin .vpshufb .l128 .xmm14 .xmm14 .xmm0),
   .vop (.vbin .vpaddd .l128 .xmm13 .xmm14 .xmm15), .vop (.vinserti128 .xmm14 .xmm14 .xmm13 1),
   .movImm64 .rax 2, .vop (.vmovq .xmm15 .rax), .vop (.vinserti128 .xmm15 .xmm15 .xmm15 1),
   .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi),
   .mov .rax (.reg .rdx), .mov .rdx (.reg .r8)]

/-- The powers, stored to `scratch`, and the registers for the loop. -/
def setup : List Instr := setupG ++ storesK .r11 pregs 0 ++ setupC

/-- Eight blocks encrypted into the data blocks `2j`… at `rdx + 32 j`, the
GHASH loads `g i` after round `i`. -/
def batch (j : Nat) (g : Nat → List Instr) : Prog isa :=
  .seq (.block (ctrsK .xmm14 .xmm0 .xmm15 aregs))
    (.seq (aesK .xmm13 aregs g) (.block (xorDataK .xmm13 .rdx aregs j)))

/-- The order of the GHASH loads of an encryption body: the product with `Y`
last. -/
def ordE : Nat → Nat
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 7 | _ => 0

/-- The order of the GHASH loads of a decryption body: blocks 0–7 (the product
with `Y` last) while the first batch is decrypted, before it overwrites them,
then blocks 8–15. -/
def ordD : Nat → Nat
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | _ => 7

/-- The GHASH work between the rounds of a batch: loads `base … base + 3` of
the order `ord` after rounds 1–4, and, if `fin`, the reduction of both lanes
and their sum into `Y` after round 5. -/
def gq (ord : Nat → Nat) (base : Nat) (fin : Bool) (j : Nat) : List Instr :=
  if 1 ≤ j ∧ j ≤ 4 then ghLoad (ord (base + j - 1))
  else if fin ∧ j = 5 then reduce .xmm7 ++ combine else []

/-- The GHASH loads of the first batch. -/
def gA : Nat → List Instr := gq ordE 0 false

/-- The GHASH loads of the second batch, the product with `Y` last, and the
reduction. -/
def gB : Nat → List Instr := gq ordE 4 true

/-- The first group, encrypted only. -/
def first : Prog isa := .seq (batch 0 fun _ => []) (batch 4 fun _ => [])

/-- A group encrypted (at `rdx + 256`) and the previous one hashed (at `rdx`). -/
def body : Prog isa :=
  .seq (.block zero)
    (.seq (batch 8 gA)
      (.seq (batch 12 gB)
        (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)])))

/-- The counter stored. -/
def storeCtr : List Instr :=
  [.vop (.vbin .vpshufb .l128 .xmm13 .xmm14 .xmm0), .vmovdquStore .l128 (at_ .rax 0) .xmm13]

/-- The last group hashed, at `rdx`. -/
def lastG : List Instr :=
  zero ++ (List.range 8).flatMap (fun i => ghLoad (ordE i)) ++ reduce .xmm7 ++ combine

/-- `Y` stored, and the upper lanes cleared. -/
def storeY : List Instr :=
  [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0), .vmovdquStore .l128 (at_ .rcx 0) .xmm2, .vop .vzeroupper]

/-- `n` (a multiple of 16, at least 16) blocks. -/
def enc : Prog isa :=
  .seq (.block setup)
    (.seq first
      (.seq (.block [.alu .cmp .r9 (.imm 32)])
        (.seq (.ite .b (.block []) (.loop body .ae))
          (.block (storeCtr ++ lastG ++ storeY)))))

/-! ## Decryption: each group hashed while it is decrypted -/

/-- The GHASH loads of the first batch of a decryption body: blocks 0–7 of
the group, read before the batch overwrites them. -/
def dA : Nat → List Instr := gq ordD 0 false

/-- The GHASH loads of the second batch: blocks 8–15, then the reduction. -/
def dB : Nat → List Instr := gq ordD 4 true

/-- A group hashed and decrypted, at `rdx`. -/
def dbody : Prog isa :=
  .seq (.block zero)
    (.seq (batch 0 dA)
      (.seq (batch 4 dB)
        (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 16)])))

/-- `n` (a multiple of 16, at least 16) blocks. -/
def dec : Prog isa :=
  .seq (.block setup)
    (.seq (.loop dbody .ae)
      (.block (storeCtr ++ storeY)))

end VG.Impl.Gcm.X86_64.Stitch
