import VerifiedGarbage.Impl.MlKem.X86_64.Arith
import VerifiedGarbage.Impl.MlKem.X86_64.Encode12
import VerifiedGarbage.Impl.MlKem.X86_64.Cbd
import VerifiedGarbage.Impl.MlKem.X86_64.Compress
import VerifiedGarbage.Impl.MlKem.X86_64.Mul
import VerifiedGarbage.Impl.MlKem.X86_64.Ntt
import VerifiedGarbage.Impl.MlKem.X86_64.Sample

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
1024 (64 bytes), of `H` at 1088 (32 bytes), of `PRF` at 1120 (128 bytes),
the message of decapsulation at 1248 (32 bytes), and its key `K̄` at 1280
(32 bytes); the working space of the primitives at 2048 (2048 bytes); and
28 polynomials of 1024 bytes from 4096 (`P k`).
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
def oPB : Nat := 1120
def oM : Nat := 1248
def oKB : Nat := 1280
def oSS : Nat := 2048
/-- Polynomial `k`. -/
def oP (k : Nat) : Nat := 4096 + 1024 * k
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
  .seq (.block (lea .rdi f ++ lea .rsi (sc oSS))) (.call "vg_mlkem_ntt_inv" nttInv)

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

/-- `f a, f (a + 1), …, f (a + n - 1)`, in sequence. -/
def seqR (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (f a) (seqR f (a + 1) n)

/-- The nine entries of `Â`, row by row (entry `e = 3i + j`). -/
def samples : Prog isa := seqR (fun e => sampleIJ (e / 3) (e % 3)) 0 9

/-- `c` if every `SampleNTT` so far succeeded (`r15 ≠ 0`). -/
def ifOk (c : Prog isa) : Prog isa :=
  .seq (.block [.alu32 .test .r15 (.reg .r15)]) (.ite .ne c (.block []))

/-- `SamplePolyCBD₂(PRF₂(σ, N))` to `f`, with `σ` at `sig`. -/
def prfCbd (sig : Ptr) (N : Nat) (f : Ptr) : Prog isa :=
  .seq (.block (setB (sc oNB) N))
    (.seq (hashAt [(sig, 32), (sc oNB, 1)] 136 0x1f (sc oPB) 128) (cbd2At (sc oPB) f))

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
