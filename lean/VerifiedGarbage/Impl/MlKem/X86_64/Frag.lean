import VerifiedGarbage.Impl.MlKem.X86_64.Arith
import VerifiedGarbage.Impl.MlKem.X86_64.Encode12
import VerifiedGarbage.Impl.MlKem.X86_64.Cbd
import VerifiedGarbage.Impl.MlKem.X86_64.Compress
import VerifiedGarbage.Impl.MlKem.X86_64.Mul
import VerifiedGarbage.Impl.MlKem.X86_64.Ntt
import VerifiedGarbage.Impl.MlKem.X86_64.Sample
import VerifiedGarbage.Impl.MlKem.X86_64.Sample4

/-!
# ML-KEM-768 on x86-64: the pieces of the top-level functions

`vg_mlkem768_keygen`, `vg_mlkem768_encaps` and `vg_mlkem768_decaps` are
sequences of calls of the polynomial primitives and the SHA-3 sponge
functions, on buffers in their working space `scratch` (whose address they
keep in `rbx`) and their arguments (whose addresses they keep in `rbp`,
`r12`, `r13` and `r14`): all callee-saved registers, which the functions
they call preserve. A buffer is at `p.1 + p.2` for a pointer `p` (a
register and an offset). Each call is preceded by the moves of its
arguments into their registers (`lea`, a `mov` and an `add`).

The layout of `scratch` (in bytes): the Keccak state at 0 (200 bytes) and
the sponge functions' working space at 200 (640 bytes); the caller's
callee-saved registers at 840 (48 bytes); a byte (`NB`, an index) at 896
and the seed of `SampleNTT` (`SB`, 34 bytes) at 904; the output of `G` at
1024 (64 bytes), of `H` at 1088 (32 bytes), the message of decapsulation
at 1248 (32 bytes), and its key `K̄` at 1280 (32 bytes); the working space
of the primitives at 2048 (2048 bytes); and 28 polynomials of 1024 bytes
from 4096 (`P k`). The outputs of `PRF₂` are in polynomial 20 (`PR`), and
the working space of their computation from polynomial 17 (which also
holds that of `vg_mlkem_sample_ntt4`).
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- A pointer: a register and an offset. -/
abbrev Ptr := Reg × Nat

/-! ## The layout of the working space -/

def oSV : Nat := 840
def oNB : Nat := 896
def oSB : Nat := 904
def oG : Nat := 1024
def oH : Nat := 1088
def oM : Nat := 1248
def oKB : Nat := 1280
def oSS : Nat := 2048
/-- Polynomial `k`. -/
def oP (k : Nat) : Nat := 4096 + 1024 * k
/-- The outputs of `PRF₂` (at most 8 of 128 bytes, in polynomial 20). -/
def oPR : Nat := oP 20
/-- The working space of `prfs` (2368 bytes, from polynomial 17), as a lane (32 bytes). -/
def lPW : Nat := oP 17 / 32
/-- The ciphertext of the re-encryption (1088 bytes, in polynomials 26 and 27). -/
def oCT : Nat := oP 26

/-- `scratch + off`. -/
abbrev sc (off : Nat) : Ptr := (.rbx, off)

/-! ## Moves -/

/-- `d ← p.1 + p.2`. -/
def lea (d : Reg) (p : Ptr) : List Instr := [.mov d (.reg p.1), .alu .add d (.imm (BitVec.ofNat 32 p.2))]

/-- The byte `v` to `p`. -/
def setB (p : Ptr) (v : Nat) : List Instr := [.mov32 .rax (.imm (BitVec.ofNat 32 v)), .store8 (at_ p.1 p.2) .rax]

/-- Copy `n` bytes from `src` to `dst`, one at a time. -/
def copy (dst src : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (lea .rdi dst ++ lea .rsi src ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 n))]))
    (.loop (.block [.movzx8 .rax (at_ .rsi 0), .store8 (at_ .rdi 0) .rax, .alu .add .rdi (.imm 1),
      .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne)

/-! ## The sponge -/

/-- Zero the Keccak state. -/
def kzero : List Instr := .mov32 .rax (.imm 0) :: zeroSt .rbx 0

/-- Absorb the `len` bytes at `src`, at position `pos` of the block of `rate` bytes. -/
def kabs (src : Ptr) (len rate pos : Nat) : Prog isa :=
  .seq (.block (lea .rdi (sc 0) ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 rate)), .mov32 .rdx (.imm (BitVec.ofNat 32 pos))] ++
      lea .rcx src ++ [.mov32 .r8 (.imm (BitVec.ofNat 32 len))] ++ lea .r9 (sc 200)))
    (.call "vg_keccak_absorb" Impl.Sha3.X86_64.Stream.absorb)

/-- Pad, at position `pos`, with the suffix `suffix`. -/
def kpad (rate pos suffix : Nat) : Prog isa :=
  .seq (.block (lea .rdi (sc 0) ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 rate)), .mov32 .rdx (.imm (BitVec.ofNat 32 pos)),
      .mov32 .rcx (.imm (BitVec.ofNat 32 suffix))] ++ lea .r8 (sc 200)))
    (.call "vg_keccak_pad" Impl.Sha3.X86_64.Stream.pad)

/-- Squeeze `len` bytes from position 0 to `dst`. -/
def ksqz (rate : Nat) (dst : Ptr) (len : Nat) : Prog isa :=
  .seq (.block (lea .rdi (sc 0) ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 rate)), .mov32 .rdx (.imm 0)] ++
      lea .rcx dst ++ [.mov32 .r8 (.imm (BitVec.ofNat 32 len))] ++ lea .r9 (sc 200)))
    (.call "vg_keccak_squeeze" Impl.Sha3.X86_64.Stream.squeeze)

/-- Absorb the pieces `ps`, from position `pos` of the block. -/
def absAll (rate : Nat) : List (Ptr × Nat) → Nat → Prog isa
  | [], _ => .block []
  | (p, l) :: ps, pos => .seq (kabs p l rate pos) (absAll rate ps ((pos + l) % rate))

/-- The total length of the pieces. -/
def totLen (ps : List (Ptr × Nat)) : Nat := (ps.map (·.2)).sum

/-- A SHA-3 function or SHAKE (of rate `rate`, with the suffix `suffix`) of
the concatenation of the pieces `ps`, `len` bytes of it to `out`. -/
def hashAt (ps : List (Ptr × Nat)) (rate suffix : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  .seq (.block kzero) (.seq (absAll rate ps 0) (.seq (kpad rate (totLen ps % rate) suffix) (ksqz rate out len)))

/-! ## The polynomial primitives -/

def nttAt (f : Ptr) : Prog isa :=
  .seq (.block (lea .rdi f ++ lea .rsi (sc oSS))) (.call "vg_mlkem_ntt" ntt)

def nttInvAt (f : Ptr) : Prog isa :=
  .seq (.block (lea .rdi f ++ lea .rsi (sc oSS))) (.call "vg_mlkem_inv_ntt" nttInv)

def mulAt (h f g : Ptr) : Prog isa :=
  .seq (.block (lea .rdi h ++ lea .rsi f ++ lea .rdx g ++ lea .rcx (sc oSS)))
    (.call "vg_mlkem_multiply_ntts" multiplyNTTs)

def addAt (f g : Ptr) : Prog isa := .seq (.block (lea .rdi f ++ lea .rsi g)) (.call "vg_mlkem_add" add)

def subAt (f g : Ptr) : Prog isa := .seq (.block (lea .rdi f ++ lea .rsi g)) (.call "vg_mlkem_sub" sub)

def cbd2At (b f : Ptr) : Prog isa := .seq (.block (lea .rdi b ++ lea .rsi f)) (.call "vg_mlkem_cbd2" cbd2)

def enc12At (f out : Ptr) : Prog isa :=
  .seq (.block (lea .rdi f ++ lea .rsi out)) (.call "vg_mlkem_encode12" encode12)

def dec12At (b f : Ptr) : Prog isa :=
  .seq (.block (lea .rdi b ++ lea .rsi f)) (.call "vg_mlkem_decode12" decode12)

def ceAt (f : Ptr) (d : Nat) (out : Ptr) : Prog isa :=
  .seq (.block (lea .rdi f ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 d))] ++ lea .rdx out ++
      [.mov32 .rcx (.imm (BitVec.ofNat 32 (32 * d)))]))
    (.call "vg_mlkem_compress_encode" compressEncode)

def ddAt (b : Ptr) (d : Nat) (f : Ptr) : Prog isa :=
  .seq (.block (lea .rdi b ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 (32 * d))), .mov32 .rdx (.imm (BitVec.ofNat 32 d))] ++
      lea .rcx f))
    (.call "vg_mlkem_decode_decompress" decodeDecompress)

/-- `SampleNTT` of the seed at `SB` to `a`, and `r15 ← r15 ∧ result`. -/
def sampleAt (a : Ptr) : Prog isa :=
  .seq (.block (lea .rdi (sc oSB) ++ lea .rsi a ++ lea .rdx (sc oSS)))
    (.seq (.call "vg_mlkem_sample_ntt" sampleNTT) (.block [.alu32 .and .r15 (.reg .rax)]))

/-! ## The matrix and the other polynomials -/

/-- Polynomial `k` of the working space. -/
abbrev pS (k : Nat) : Ptr := sc (oP k)

/-- `Â[i, j]`: polynomial `6 + 3i + j`. -/
abbrev aS (i j : Nat) : Ptr := pS (6 + 3 * i + j)

/-- `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)`, with `ρ` at `SB`. -/
def sampleIJ (i j : Nat) : Prog isa :=
  .seq (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i)) (sampleAt (aS i j))

/-- Seed `k` of four, `ρ ‖ j ‖ i` with `ρ` at `SB`, to `34 k` bytes into `scratch`. -/
def seedAt (k i j : Nat) : Prog isa :=
  .seq (copy (sc (34 * k)) (sc oSB) 32) (.block (setB (sc (34 * k + 32)) j ++ setB (sc (34 * k + 33)) i))

/-- `f a, f (a + 1), …, f (a + n - 1)`, in sequence. -/
def seqR (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (f a) (seqR f (a + 1) n)

/-! ## `PRF₂`, several at once -/

/-- `σ` (or `r`): the second half of `G`'s output. -/
abbrev sigP : Ptr := sc (oG + 32)

/-- `PRF₂(σ, N)` (128 bytes) to `out`, with `σ` at `G + 32`. -/
def prf1 (N : Nat) (out : Ptr) : Prog isa :=
  .seq (.block (setB (sc oNB) N)) (hashAt [(sigP, 32), (sc oNB, 1)] 136 0x1f out 128)

/-- `PRF₂(σ, N₀ + i)` to `scratch + o + 128 i` for each `i < n`, one at a
time (the working space at lane `wl` is not used). -/
def prfsScalar (N₀ n o _wl : Nat) : Prog isa := seqR (fun i => prf1 (N₀ + i) (sc (o + 128 * i))) 0 n

namespace Prf4

open VG.Impl.Sha3.X86_64.X4 (vb st permute4 rcTable)

/-! Four instances of `PRF₂` at once, in the four 64-bit elements of `ymm`
registers (`Impl/Sha3/X86_64/X4.lean`), in 2368 bytes of working space
from lane `wl` of `scratch` (byte `32 wl`): the four states (interleaved,
800 bytes), the second buffer of the permutation (800 bytes) and the table
of the round constants (768 bytes). The input `σ ‖ N` is 33 bytes, and the
128 bytes of output fewer than the rate of SHAKE256 (136), so the padded
input is one block and the output its permutation's first 128 bytes. -/

/-- The four states, zeroed. -/
def zero (wl : Nat) : List Instr :=
  vb .vpxor .xmm0 .xmm0 .xmm0 :: (List.range 25).flatMap fun i => [st .rbx (wl + i) .xmm0]

/-- Lanes 0–3 of each state: the 32 bytes of `σ`. -/
def sigLanes (wl : Nat) : List Instr :=
  (List.range 4).flatMap fun i => .mov .rax (.mem (at_ .rbx (oG + 32 + 8 * i))) ::
    (List.range 4).flatMap fun k => [.store (at_ .rbx (32 * (wl + i) + 8 * k)) .rax]

/-- Byte 32 of state `k`: the index `N₀ + k`. -/
def nonces (N₀ wl : Nat) : List Instr :=
  (List.range 4).flatMap fun k =>
    [.mov32 .rax (.imm (BitVec.ofNat 32 (N₀ + k))), .store8 (at_ .rbx (32 * (wl + 4) + 8 * k)) .rax]

/-- SHAKE's suffix `0x1f` at byte 33 of each state, and the last bit of the
padding (`0x80`) at byte 135. -/
def pads (wl : Nat) : List Instr :=
  .mov32 .rax (.imm 0x1f) :: ((List.range 4).flatMap fun k => [.store8 (at_ .rbx (32 * (wl + 4) + 8 * k + 1)) .rax]) ++
    .mov32 .rax (.imm 0x80) :: (List.range 4).flatMap fun k => [.store8 (at_ .rbx (32 * (wl + 16) + 8 * k + 7)) .rax]

/-- The arguments of `permute4`. -/
def args (wl : Nat) : List Instr :=
  [.mov .rdi (.reg .rbx), .alu .add .rdi (.imm (BitVec.ofNat 32 (32 * wl))), .mov .rsi (.reg .rbx),
    .alu .add .rsi (.imm (BitVec.ofNat 32 (32 * (wl + 25)))), .mov .rdx (.reg .rbx),
    .alu .add .rdx (.imm (BitVec.ofNat 32 (32 * (wl + 50)))), .mov .rcx (.reg .rbx),
    .alu .add .rcx (.imm (BitVec.ofNat 32 (32 * (wl + 74))))]

/-- The first 128 bytes of states `0, …, m - 1` to `scratch + o + 128 k`. -/
def extract (m o wl : Nat) : List Instr :=
  (List.range m).flatMap fun k => (List.range 16).flatMap fun i =>
    [.mov .rax (.mem (at_ .rbx (32 * (wl + i) + 8 * k))), .store (at_ .rbx (o + 128 * k + 8 * i)) .rax]

/-- The table, the padded inputs and the arguments of the permutation. -/
def setup (N₀ wl : Nat) : List Instr :=
  rcTable .rbx (wl + 50) ++ zero wl ++ sigLanes wl ++ nonces N₀ wl ++ pads wl ++ args wl

/-- `PRF₂(σ, N₀ + k)` to `scratch + o + 128 k` for each `k < m` (at most
four), at once. After the copies, `vzeroupper` clears the upper halves of
the vector registers, so that the SSE code that runs next does not pay for
mixing them. -/
def batch (N₀ m o wl : Nat) : Prog isa :=
  .seq (.block (setup N₀ wl)) (.seq permute4 (.block (extract m o wl ++ [.vop .vzeroupper])))

end Prf4

/-- `PRF₂(σ, N₀ + i)` to `scratch + o + 128 i` for each `i < n`, four at a
time (the last `n mod 4` with lanes whose outputs are not copied). -/
def prfsX4 : Nat → Nat → Nat → Nat → Prog isa
  | _, 0, _, _ => .block []
  | N₀, 1, o, wl => Prf4.batch N₀ 1 o wl
  | N₀, 2, o, wl => Prf4.batch N₀ 2 o wl
  | N₀, 3, o, wl => Prf4.batch N₀ 3 o wl
  | N₀, n + 4, o, wl => .seq (Prf4.batch N₀ 4 o wl) (prfsX4 (N₀ + 4) n (o + 512) wl)

/-- How many of `n` outputs `prfsAvx2` computes one at a time, first:
`n mod 4` when it is 1 or 2. (Four instances at once cost about as much as
two on their own, so this is as fast as running them with lanes whose
outputs are not copied, and the code is shorter; three are four at a time.) -/
def prfsLead (n : Nat) : Nat := if n % 4 = 1 ∨ n % 4 = 2 then n % 4 else 0

/-- `PRF₂(σ, N₀ + i)` to `scratch + o + 128 i` for each `i < n`, with AVX2:
the first `prfsLead n` one at a time, and the others four at a time. -/
def prfsAvx2 (N₀ n o wl : Nat) : Prog isa :=
  .seq (prfsScalar N₀ (prfsLead n) o wl) (prfsX4 (N₀ + prfsLead n) (n - prfsLead n) (o + 128 * prfsLead n) wl)

/-- An implementation of `vg_mlkem_sample_ntt4` to call (its symbol and its
code), and of the computation of several outputs of `PRF₂` that goes with
it, which its callers inline: `prfs N₀ n o wl` writes `PRF₂(σ, N₀ + i)`
(with `σ` at `G + 32`) to `scratch + o + 128 i` for each `i < n`, with the
working space from lane `wl` of `scratch`. The top-level functions, which
use both, are emitted once for each (`Generic/MlKemSample4/X86_64/`). -/
structure Callee4 where
  name : String
  code : Prog isa
  prfs : Nat → Nat → Nat → Nat → Prog isa

def Callee4.scalar : Callee4 := ⟨"vg_mlkem_sample_ntt4", Sample4.sampleNTT4, prfsScalar⟩
def Callee4.avx2 : Callee4 := ⟨"vg_mlkem_sample_ntt4_avx2", Sample4.sampleNTT4Avx2, prfsAvx2⟩

/-- `SampleNTT` of the four seeds at `scratch` to the four polynomials from
`a`, with the working space `scr` (8192 bytes), and `r15 ← r15 ∧ result`. -/
def sample4At (c : Callee4) (a scr : Ptr) : Prog isa :=
  .seq (.block (lea .rdi (sc 0) ++ lea .rsi a ++ lea .rdx scr))
    (.seq (.call c.name c.code) (.block [.alu32 .and .r15 (.reg .rax)]))

/-- Entries `e₀, …, e₀ + 3` of a matrix of `n` columns (entry `e = n i + j`),
from polynomial `a`, with `SampleNTT` on the four seeds at once. -/
def quad (c : Callee4) (n e₀ : Nat) (a scr : Ptr) : Prog isa :=
  .seq (seedAt 0 (e₀ / n) (e₀ % n)) (.seq (seedAt 1 ((e₀ + 1) / n) ((e₀ + 1) % n))
    (.seq (seedAt 2 ((e₀ + 2) / n) ((e₀ + 2) % n)) (.seq (seedAt 3 ((e₀ + 3) / n) ((e₀ + 3) % n))
      (sample4At c a scr))))

/-- The nine entries of `Â`, row by row (entry `e = 3i + j`): four at a
time, with polynomials 17–24 as the working space, and the last on its own. -/
def samples (c : Callee4) : Prog isa :=
  .seq (quad c 3 0 (aS 0 0) (pS 17)) (.seq (quad c 3 4 (aS 1 1) (pS 17)) (sampleIJ 2 2))

/-- `c` if every `SampleNTT` so far succeeded (`r15 ≠ 0`). -/
def ifOk (c : Prog isa) : Prog isa :=
  .seq (.block [.alu32 .test .r15 (.reg .r15)]) (.ite .ne c (.block []))

/-- `f[0] ×_T g[0] + f[1] ×_T g[1] + f[2] ×_T g[2]` to polynomial 15 (with 16 for the products). -/
def dotAt (f g : Nat → Ptr) : Prog isa :=
  .seq (mulAt (pS 15) (f 0) (g 0)) (.seq (mulAt (pS 16) (f 1) (g 1)) (.seq (addAt (pS 15) (pS 16))
    (.seq (mulAt (pS 16) (f 2) (g 2)) (addAt (pS 15) (pS 16)))))

/-! ## Entry and exit -/

/-- The callee-saved registers the top-level functions save, at `scratch + 840 + 8k`. -/
def savedRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Save the callee-saved registers in the working space at `scr`, keep `scr`
in `rbx` and the pointers in the other registers (`moves`), and `r15 ← 1`. -/
def topPro (scr : Reg) (moves : List (Reg × Reg)) : List Instr :=
  (List.range 6).map (fun k => .store (at_ scr (oSV + 8 * k)) (savedRegs.getD k .rbx)) ++
    [.mov .rbx (.reg scr)] ++ moves.map (fun m => .mov m.1 (.reg m.2)) ++ [.mov32 .r15 (.imm 1)]

/-- Return `r15`, and restore the callee-saved registers (`rbx` last). -/
def topEpi : List Instr :=
  .mov32 .rax (.reg .r15) ::
    ((List.range 5).map fun k => .mov (savedRegs.getD (5 - k) .rbx) (.mem (at_ .rbx (oSV + 8 * (5 - k))))) ++
    [.mov .rbx (.mem (at_ .rbx oSV))]

end VG.Impl.MlKem.X86_64
