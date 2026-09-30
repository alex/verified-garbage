import VerifiedGarbage.Impl.MlKem.X86_64.Sample
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on x86-64: the pieces of `vg_mldsa*_verify`

`vg_mldsa44_verify`, `vg_mldsa65_verify` and `vg_mldsa87_verify` are
sequences of calls of the polynomial primitives (`vg_mldsa_*`) and of the
SHA-3 sponge functions, on buffers in their working space `scratch` (whose
address they keep in `rbx`) and their arguments `pk`, `mu` and `sig` (in
`rbp`, `r12` and `r13`): all callee-saved registers, which the functions
they call preserve. A buffer is at `p.1 + p.2` for a pointer `p` (a register
and an offset). Each call is preceded by the moves of its arguments into
their registers (`glue`: a `mov` and an `add` for a pointer, a `mov` for an
integer).

The code is generic in the primitives it calls (`Prims`, their code), so
that it can be proven for any implementations of them.

The layout of `scratch` (in bytes): the Keccak state at 0 (200 bytes) and
the sponge functions' working space at 200 (640 bytes); the caller's
callee-saved registers at 840 (48 bytes); the seed of `RejNTTPoly` (`SB`,
34 bytes) at 896; `w1Encode(w′₁)` at 1024 (at most 1024 bytes); the
recomputed commitment hash `c̃′` at 2048 (at most 64 bytes); the working
space of the primitives at 4096 (2048 bytes); and polynomials of 1024 bytes
from 8192 (`P j`): the hint `h` (polynomials 0 to 7, of which the first
`k`), `z` (8 to 14), `c` (15), two temporaries (16, 17), `w′` (18), `w′₁`
(19), and `Â[r, s]` (`20 + 8r + s`).
-/

namespace VG.Impl.MlDsa.X86_64.Verify

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)

/-- A pointer: a register and an offset. -/
abbrev Ptr := Reg × Nat

/-! ## The layout of the working space -/

def oSV : Nat := 840
def oSB : Nat := 896
def oB : Nat := 1024
def oCT : Nat := 2048
def oSS : Nat := 4096
/-- Polynomial `j`. -/
def oP (j : Nat) : Nat := 8192 + 1024 * j

/-- `scratch + off`. -/
abbrev sc (off : Nat) : Ptr := (.rbx, off)

/-- Polynomial `j` of the working space. -/
abbrev pS (j : Nat) : Ptr := sc (oP j)

abbrev pH (r : Nat) : Ptr := pS r
abbrev pZ (i : Nat) : Ptr := pS (8 + i)
abbrev pC : Ptr := pS 15
abbrev pT : Ptr := pS 16
abbrev pT2 : Ptr := pS 17
abbrev pW : Ptr := pS 18
abbrev pW1 : Ptr := pS 19
abbrev pA (r s : Nat) : Ptr := pS (20 + 8 * r + s)

/-! ## Moves -/

/-- An argument: a pointer, or an integer (an immediate). -/
inductive Arg
  | ptr (p : Ptr)
  | imm (v : Nat)

/-- `d ← a`. -/
def Arg.instrs (d : Reg) : Arg → List Instr
  | .ptr p => [.mov d (.reg p.1), .alu .add d (.imm (BitVec.ofNat 32 p.2))]
  | .imm v => [.mov32 d (.imm (BitVec.ofNat 32 v))]

/-- The moves of the arguments `as` into their registers. -/
def glue : List (Reg × Arg) → List Instr
  | [] => []
  | (d, a) :: as => a.instrs d ++ glue as

/-- The moves of the arguments, then a call. -/
def callAt (name : String) (c : Prog isa) (as : List (Reg × Arg)) : Prog isa :=
  .seq (.block (glue as)) (.call name c)

/-- The byte `v` to `p`. -/
def setB (p : Ptr) (v : Nat) : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 v)), .store8 (at_ p.1 p.2) .rax]

/-- Copy `n` bytes from `src` to `dst`, one at a time. -/
def copy (dst src : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (glue [(.rdi, .ptr dst), (.rsi, .ptr src), (.rcx, .imm n)]))
    (.loop (.block [.movzx8 .rax (at_ .rsi 0), .store8 (at_ .rdi 0) .rax, .alu .add .rdi (.imm 1),
      .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne)

/-! ## The sponge -/

/-- Zero the Keccak state. -/
def kzero : List Instr := .mov32 .rax (.imm 0) :: Impl.MlKem.X86_64.zeroSt .rbx 0

/-- Absorb the `len` bytes at `src`, at position `pos` of the block of `rate` bytes. -/
def kabs (src : Ptr) (len rate pos : Nat) : Prog isa :=
  callAt "vg_keccak_absorb" Impl.Sha3.X86_64.Stream.absorb
    [(.rdi, .ptr (sc 0)), (.rsi, .imm rate), (.rdx, .imm pos), (.rcx, .ptr src), (.r8, .imm len),
      (.r9, .ptr (sc 200))]

/-- Pad, at position `pos`, with the suffix `suffix`. -/
def kpad (rate pos suffix : Nat) : Prog isa :=
  callAt "vg_keccak_pad" Impl.Sha3.X86_64.Stream.pad
    [(.rdi, .ptr (sc 0)), (.rsi, .imm rate), (.rdx, .imm pos), (.rcx, .imm suffix), (.r8, .ptr (sc 200))]

/-- Squeeze `len` bytes from position 0 to `dst`. -/
def ksqz (rate : Nat) (dst : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_keccak_squeeze" Impl.Sha3.X86_64.Stream.squeeze
    [(.rdi, .ptr (sc 0)), (.rsi, .imm rate), (.rdx, .imm 0), (.rcx, .ptr dst), (.r8, .imm len),
      (.r9, .ptr (sc 200))]

/-- `H(a ‖ b, len)` (SHAKE256) of the `la` bytes at `a` and the `lb` bytes at
`b`, to `out`. -/
def hash2 (a : Ptr) (la : Nat) (b : Ptr) (lb : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  .seq (.block kzero) (.seq (kabs a la 136 0) (.seq (kabs b lb 136 (la % 136))
    (.seq (kpad 136 ((la + lb) % 136) 0x1f) (ksqz 136 out len))))

/-! ## The primitives -/

/-- The code of the primitives `vg_mldsa_*` that verification calls. -/
structure Prims where
  ntt : Prog isa
  invNtt : Prog isa
  mul : Prog isa
  mulAdd : Prog isa
  sub : Prog isa
  rejNtt : Prog isa
  ball : Prog isa
  useHint : Prog isa
  simpleBitPack : Prog isa
  bitUnpack : Prog isa
  unpackT1 : Prog isa
  hintUnpack : Prog isa
  normLt : Prog isa

section
variable (P : Prims)

def nttAt (f : Ptr) : Prog isa := callAt "vg_mldsa_ntt" P.ntt [(.rdi, .ptr f), (.rsi, .ptr (sc oSS))]

def invNttAt (f : Ptr) : Prog isa :=
  callAt "vg_mldsa_inv_ntt" P.invNtt [(.rdi, .ptr f), (.rsi, .ptr (sc oSS))]

def mulAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_ntt" P.mul [(.rdi, .ptr h), (.rsi, .ptr f), (.rdx, .ptr g)]

def mulAddAt (h f g : Ptr) : Prog isa :=
  callAt "vg_mldsa_multiply_add_ntt" P.mulAdd [(.rdi, .ptr h), (.rsi, .ptr f), (.rdx, .ptr g)]

def subAt (f g : Ptr) : Prog isa := callAt "vg_mldsa_sub" P.sub [(.rdi, .ptr f), (.rsi, .ptr g)]

def rejNttAt (a : Ptr) : Prog isa :=
  callAt "vg_mldsa_rej_ntt_poly" P.rejNtt [(.rdi, .ptr (sc oSB)), (.rsi, .ptr a), (.rdx, .ptr (sc oSS))]

def ballAt (ct : Ptr) (len tau : Nat) (c : Ptr) : Prog isa :=
  callAt "vg_mldsa_sample_in_ball" P.ball
    [(.rdi, .ptr ct), (.rsi, .imm len), (.rdx, .imm tau), (.rcx, .ptr c), (.r8, .ptr (sc oSS))]

def useHintAt (h r : Ptr) (g2 : Nat) (out : Ptr) : Prog isa :=
  callAt "vg_mldsa_use_hint" P.useHint [(.rdi, .ptr h), (.rsi, .ptr r), (.rdx, .imm g2), (.rcx, .ptr out)]

def sbpAt (f : Ptr) (b : Nat) (out : Ptr) (len : Nat) : Prog isa :=
  callAt "vg_mldsa_simple_bit_pack" P.simpleBitPack
    [(.rdi, .ptr f), (.rsi, .imm b), (.rdx, .ptr out), (.rcx, .imm len)]

def bitUnpackAt (v : Ptr) (len a b : Nat) (f : Ptr) : Prog isa :=
  callAt "vg_mldsa_bit_unpack" P.bitUnpack
    [(.rdi, .ptr v), (.rsi, .imm len), (.rdx, .imm a), (.rcx, .imm b), (.r8, .ptr f)]

def unpackT1At (v f : Ptr) : Prog isa :=
  callAt "vg_mldsa_unpack_t1" P.unpackT1 [(.rdi, .ptr v), (.rsi, .ptr f)]

def hintUnpackAt (y : Ptr) (len omega : Nat) (h : Ptr) (hlen : Nat) : Prog isa :=
  callAt "vg_mldsa_hint_bit_unpack" P.hintUnpack
    [(.rdi, .ptr y), (.rsi, .imm len), (.rdx, .imm omega), (.rcx, .ptr h), (.r8, .imm hlen)]

def normLtAt (f : Ptr) (bound : Nat) : Prog isa :=
  callAt "vg_mldsa_norm_lt" P.normLt [(.rdi, .ptr f), (.rsi, .imm bound)]

end

/-! ## Results -/

/-- `r15 ← r15 ∧ eax`. -/
def and15 : List Instr := [.alu32 .and .r15 (.reg .rax)]

/-- The polynomial at `a` masked by the result `eax` (0 or 1) of the
sampler that wrote it: unchanged if 1, and zero if 0, so that it is reduced
either way, without a branch. `edx ← -eax`, then each coefficient `∧ edx`. -/
def mask (a : Ptr) : Prog isa :=
  .seq (.block ([.mov32 .rdx (.imm 0), .alu32 .sub .rdx (.reg .rax)] ++
      glue [(.rdi, .ptr a), (.rcx, .imm 256)]))
    (.loop (.block [.mov32 .rax (.mem (at_ .rdi 0)), .alu32 .and .rax (.reg .rdx), .store32 (at_ .rdi 0) .rax,
      .alu .add .rdi (.imm 4), .alu .sub .rcx (.imm 1)]) .ne)

/-- A sampler's call, its result ANDed into `r15`, and its output masked. -/
def sampled (call : Prog isa) (a : Ptr) : Prog isa :=
  .seq call (.seq (.block and15) (mask a))

/-- `c` if `r15 ≠ 0`. -/
def ifOk (c : Prog isa) : Prog isa :=
  .seq (.block [.alu32 .test .r15 (.reg .r15)]) (.ite .ne c (.block []))

/-- `f a, f (a + 1), …, f (a + n - 1)`, in sequence. -/
def seqR (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (f a) (seqR f (a + 1) n)

/-- The OR of the XORs of the `n` bytes at `rsi` and `rdi`, to `rdx`. -/
def cmpBody : Prog isa :=
  .block [.movzx8 .rax (at_ .rsi 0), .movzx8 .r8 (at_ .rdi 0), .alu .xor .rax (.reg .r8), .alu .or .rdx (.reg .rax),
    .alu .add .rsi (.imm 1), .alu .add .rdi (.imm 1), .alu .sub .rcx (.imm 1)]

/-- `r15 ← 0` unless the `n` bytes at `a` and `b` are equal, without a
branch: `rdx` is the OR of the XORs of their bytes, so 0 exactly when they
are equal (`sub rdx, 1` borrows then), and `rax` the mask `-borrow`. -/
def cmpAnd (a b : Ptr) (n : Nat) : Prog isa :=
  .seq (.block (glue [(.rsi, .ptr a), (.rdi, .ptr b), (.rcx, .imm n)] ++ [.mov32 .rdx (.imm 0)]))
    (.seq (.loop cmpBody .ne) (.block ([.alu .sub .rdx (.imm 1), .alu .sbb .rax (.reg .rax)] ++ and15)))

/-! ## Entry and exit -/

/-- The callee-saved registers, saved at `scratch + 840 + 8k`. -/
def savedRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Save the callee-saved registers in the working space at `rcx`, keep it
in `rbx`, `pk` in `rbp`, `mu` in `r12` and `sig` in `r13`, and `r15 ← 1`. -/
def pro : List Instr :=
  (List.range 6).map (fun k => .store (at_ .rcx (oSV + 8 * k)) (savedRegs.getD k .rbx)) ++
    [.mov .rbx (.reg .rcx), .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx),
      .mov32 .r15 (.imm 1)]

/-- Return `r15`, and restore the callee-saved registers (`rbx` last). -/
def epi : List Instr :=
  .mov32 .rax (.reg .r15) ::
    ((List.range 5).map fun k => .mov (savedRegs.getD (5 - k) .rbx) (.mem (at_ .rbx (oSV + 8 * (5 - k))))) ++
    [.mov .rbx (.mem (at_ .rbx oSV))]

end VG.Impl.MlDsa.X86_64.Verify
