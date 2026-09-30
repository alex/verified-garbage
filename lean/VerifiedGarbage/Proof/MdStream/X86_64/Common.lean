import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.MdStream.X86_64
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming Merkle–Damgård hash functions on x86-64: common lemmas

Untrusted: everything here is checked by Lean. The contracts the generic
proofs are written against, what they need of a hash function's parameters
(`Shape`) and of its compression function (`CalleeOk`), the call of the
compression function (`compressAt`), and weakest-precondition rules for the
instructions used.
-/

namespace VG.Proof.MdStream.X86_64

open VG VG.X86_64 VG.Impl.MdStream.X86_64
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)

/-! ## Addresses and regions -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem contains_offset' {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofInt 64 (off : Int)) n := by
  rw [ofInt_natCast]; exact contains_offset h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem save_sep (p : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    Mem.Sep (p + BitVec.ofInt 64 (d : Int)) 8 (p + BitVec.ofInt 64 (e : Int)) 8 := by
  rw [ofInt_natCast, ofInt_natCast]
  exact Offset.sep p h (by omega) (by omega)

theorem readW_writeW_save (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofInt 64 (e : Int)) v).readW (p + BitVec.ofInt 64 (d : Int)) 64 =
    m.readW (p + BitVec.ofInt 64 (d : Int)) 64 :=
  Mem.readW_writeW_sep (save_sep p hd he h) (by decide)

/-! Saves at `so + d`, with the conditions on the literal offsets `d`, `e`
alone, which `decide` discharges. -/
theorem readW_writeW_save_so {so : Nat} (hso : so ≤ 1024) (m : Mem) (p : Addr) (v : BitVec 64)
    {d e : Nat} (hd : d ≤ 64) (he : e ≤ 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofInt 64 ((so + e : Nat) : Int)) v).readW
      (p + BitVec.ofInt 64 ((so + d : Nat) : Int)) 64 =
      m.readW (p + BitVec.ofInt 64 ((so + d : Nat) : Int)) 64 :=
  readW_writeW_save m p v (by omega) (by omega) (by omega)

theorem readW_writeW_save_so_l {so : Nat} (hso : so ≤ 1024) (m : Mem) (p : Addr) (v : BitVec 64)
    {e : Nat} (he : e ≤ 64) (h : 8 ≤ e) :
    (m.writeW (p + BitVec.ofInt 64 ((so + e : Nat) : Int)) v).readW (p + BitVec.ofInt 64 (so : Int)) 64 =
      m.readW (p + BitVec.ofInt 64 (so : Int)) 64 :=
  readW_writeW_save m p v (by omega) (by omega) (by omega)

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem add_ofNat (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-! ## Immediates and arithmetic -/

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega

theorem zx_ofNat {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = (1 : BitVec 64) := by decide

theorem and_mask {B : Nat} (hB : B = 64 ∨ B = 128) (x : BitVec 64) :
    x &&& (BitVec.ofNat 32 (B - 1)).signExtend 64 = BitVec.ofNat 64 (x.toNat % B) := by
  rw [sx_ofNat (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rcases hB with rfl | rfl
  · rw [show (64 - 1 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  · rw [show (128 - 1 : Nat) % 2 ^ 64 = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  rw [show BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

/-! ## Sizes -/

/-- The sizes the generic proofs support, checked for each hash function by
`decide`. -/
structure Dims (P : Params) : Prop where
  B : P.B = 64 ∨ P.B = 128
  N : 0 < P.N ∧ P.N ≤ 64
  L : 0 < P.L ∧ P.L ≤ 16
  so : P.so ≤ 1024

theorem Dims.mod {P : Params} (hd : Dims P) (n : Nat) : n % 2 ^ 64 % P.B = n % P.B := by
  rcases hd.B with h | h <;> rw [h] <;> omega

theorem Dims.pos {P : Params} (hd : Dims P) : 0 < P.B := by rcases hd.B with h | h <;> omega

/-- The shift count of `direct`. -/
theorem Dims.lg {P : Params} (hd : Dims P) :
    1 ≤ Nat.log2 P.B ∧ Nat.log2 P.B ≤ 63 ∧ 2 ^ Nat.log2 P.B = P.B := by
  rcases hd.B with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

theorem restore_eq (P : Params) : restore P = [
    .mov .rbx (.mem (at_ .r15 P.so)), .mov .rbp (.mem (at_ .r15 (P.so + 8))),
    .mov .r12 (.mem (at_ .r15 (P.so + 16))), .mov .r13 (.mem (at_ .r15 (P.so + 24))),
    .mov .r14 (.mem (at_ .r15 (P.so + 32))), .mov .r15 (.mem (at_ .r15 (P.so + 40)))] :=
  rfl

theorem save_eq (P : Params) (b : Reg) : save P b = [
    .store (at_ b P.so) .rbx, .store (at_ b (P.so + 8)) .rbp, .store (at_ b (P.so + 16)) .r12,
    .store (at_ b (P.so + 24)) .r13, .store (at_ b (P.so + 32)) .r14, .store (at_ b (P.so + 40)) .r15] :=
  rfl

/-! ## Saving the caller's registers -/

section
variable (P : Params) (s₀ : State) (b : Reg)

/-- The caller's callee-saved registers are saved in the scratch space at `b`. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved P, m.readW (s₀.gpr b + BitVec.ofInt 64 (p.2 : Int)) 64 = s₀.gpr p.1

/-- The memory after saving them. -/
def saveMem : Mem :=
  (((((s₀.mem.writeW (s₀.gpr b + BitVec.ofInt 64 ((P.so : Nat) : Int)) (s₀.gpr .rbx)).writeW
    (s₀.gpr b + BitVec.ofInt 64 ((P.so + 8 : Nat) : Int)) (s₀.gpr .rbp)).writeW
    (s₀.gpr b + BitVec.ofInt 64 ((P.so + 16 : Nat) : Int)) (s₀.gpr .r12)).writeW
    (s₀.gpr b + BitVec.ofInt 64 ((P.so + 24 : Nat) : Int)) (s₀.gpr .r13)).writeW
    (s₀.gpr b + BitVec.ofInt 64 ((P.so + 32 : Nat) : Int)) (s₀.gpr .r14)).writeW
    (s₀.gpr b + BitVec.ofInt 64 ((P.so + 40 : Nat) : Int)) (s₀.gpr .r15)

end

section
variable {P : Params} {s₀ : State} {b : Reg}

theorem saveMem_saved (hd : Dims P) : Saved P s₀ b (saveMem P s₀ b) := by
  have := hd.so
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [saveMem, Mem.readW_writeW_self64, readW_writeW_save_so this,
    readW_writeW_save_so_l this]

theorem saveMem_frame (hd : Dims P) : Frame [⟨s₀.gpr b, P.so + 48⟩] s₀.mem (saveMem P s₀ b) := by
  have := hd.so
  have c : ∀ d : Nat, d + 8 ≤ P.so + 48 →
      (⟨s₀.gpr b, P.so + 48⟩ : Region).Contains (s₀.gpr b + BitVec.ofInt 64 (d : Int)) (64 / 8) :=
    fun d hd => contains_offset' hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by omega))).writeW (List.mem_singleton_self _) _
    (c _ (by omega))).writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c _ (by omega))

/-- The saved registers are outside the part of the scratch space the
compression function uses. -/
theorem saved_offset (hd : Dims P) {p : Reg × Nat} (hp : p ∈ saved P) : P.so ≤ p.2 ∧ p.2 + 8 ≤ P.so + 48 := by
  have := hd.so
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

end

/-! ## The contracts

The generic proofs are written against these; each hash function's own
contracts are these for its instance. -/

section
variable {P : Params} (H : Md P.B P.N P.L)

/-- The contract of the compression function: updates the hash value at
`rdi` with the `rdx` blocks at `rsi`, with scratch space `rcx` (`so`
bytes). -/
def compressK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, P.N⟩
    let blocks : Region := ⟨s.gpr .rsi, P.B * (s.gpr .rdx).toNat⟩
    let scratch : Region := ⟨s.gpr .rcx, P.so⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch
  post s s' :=
    H.stateAt s'.mem (s.gpr .rdi) =
      H.compressBlocks (H.stateAt s.mem (s.gpr .rdi)) s.mem (s.gpr .rsi) (s.gpr .rdx).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

/-- The contract of `update`: if the state at `rdi` represents a message of
`rsi` bytes (modulo 2⁶⁴) from any initial hash value, it then represents
that message followed by the `rcx` bytes at `rdx`. -/
def updK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, P.N + P.B⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, P.so + 48⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, H.Repr iv s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    H.Repr iv s'.mem (s.gpr .rdi) (m ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The contract of `finalize`: if the state at `rdi` represents a message of
`rsi` bytes, writes its final hash value to `rdx` (`N` bytes). -/
def finK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, P.N + P.B⟩
    let out : Region := ⟨s.gpr .rdx, P.N⟩
    let scratch : Region := ⟨s.gpr .rcx, P.so + 48⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, H.Repr iv s.mem (s.gpr .rdi) m → H.lenOk m.length →
    s.gpr .rsi = BitVec.ofNat 64 m.length → bytesAt s'.mem (s.gpr .rdx) P.N = H.hash iv m
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end

/-! ## What each hash function's own code must do -/

/-- The length field and the digest: `P.len` stores the length field for the
byte count in `r12` at `rbx + N + B - L`, and `P.out` writes the digest of the
hash value at `rbx` to `rbp`; each writes only `rax` and the flags. -/
structure Shape {P : Params} (H : Md P.B P.N P.L) : Prop where
  len : ∀ s : State, InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L →
    WP isa (.block P.len) s fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem (s.gpr .rbx + BitVec.ofNat 64 (P.N + P.B - P.L)) (H.lenOf (s.gpr .r12))
  out : ∀ s : State, InRegions (s.rd ++ s.wr) (s.gpr .rbx) P.N → InRegions s.wr (s.gpr .rbp) P.N →
    Region.Disjoint ⟨s.gpr .rbx, P.N⟩ ⟨s.gpr .rbp, P.N⟩ →
    WP isa (.block P.out) s fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = writeBytes s.mem (s.gpr .rbp) (H.digest (H.stateAt s.mem (s.gpr .rbx)))

/-- The initial taint of `update`: the arguments and `rsp` are public, and
`rdi` and `r8` point at the writable regions. -/
def τ₀ (P : Params) : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [P.N + P.B, P.so + 48],
    bases := [(.rdi, 0, 0), (.r8, 1, 0)] }

/-- What the taint analysis proves of the pieces of `update` and `finalize`
between the calls of the compression function, for one hash function's
code: each is `⟨_, by taint_decide⟩`. -/
structure Taints (P : Params) : Prop where
  updStart : ∃ hc, (taint.check (τ₀ P) (.block (updateStart P)) hc).isSome = true
  updHead : ∃ hc, ((taint.check (X86_64.Taint.ofRegs [.rbx, .r15, .rsp, .rbp, .r12, .r13]) (updateHead P) hc).map
    fun τ' => (RegSet.ofList [.r12, .r14]).subset τ'.regs) = some true
  updEnd : ∃ hc, (taint.check (X86_64.Taint.ofRegs [.r15]) (.block (restore P)) hc).isSome = true
  finStart : ∃ hc, (taint.check (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) (finalizeStart P) hc).isSome
    = true
  finPad : ∃ hc, (taint.check (X86_64.Taint.ofRegs [.rbx, .r15, .rbp, .r12, .rsp, .r13, .r14]) (finalizePad P)
    hc).isSome = true
  finEnd : ∃ hc, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r15]) (.block (P.out ++ restore P)) hc).isSome
    = true

/-! ## The compression function -/

/-- What `compressAt` needs of the compression function it calls: that it is
correct and constant time, does not touch `rsp` or the stack, and keeps
`rdi` and `rcx`. -/
structure CalleeOk {P : Params} (H : Md P.B P.N P.L) (code : Prog isa) : Prop where
  verified : ∀ s, (compressK H).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressK H).post s s'
  ct : ConstantTime isa (compressK H).pre (compressK H).pub code
  nosp : NoSp code
  depth : code.depth = 0
  keeps_rdi : ∀ i ∈ instrs code, Taint.clobbers i .rdi = false
  keeps_rcx : ∀ i ∈ instrs code, Taint.clobbers i .rcx = false

/-- The facts about the instructions of `code`, from one kernel check each. -/
theorem CalleeOk.of_verified {P : Params} {H : Md P.B P.N P.L} {code : Prog isa}
    (hv : ∀ s, (compressK H).pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressK H).post s s')
    (hct : ConstantTime isa (compressK H).pre (compressK H).pub code)
    (hk : ((instrs code).all fun i => !Taint.clobbers i .rdi && !Taint.clobbers i .rcx &&
      !Taint.clobbers i .rsp) = true)
    (hd : code.depth = 0) : CalleeOk H code := by
  have h := fun i hi => List.all_eq_true.mp hk i hi
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨hv, hct, fun i hi => (h i hi).2, hd, fun i hi => (h i hi).1.1, fun i hi => (h i hi).1.2⟩

/-- A region disjoint from the return address of a call reads the same on
entry to the callee. -/
theorem callEntry_byte (s : State) {R : Region} (hd : (below (s.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    s.callEntry.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (s.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

/-- What the call of the compression function in `compressWith` needs of the
state `s` before it: the hash value `st` at `rbx`, the scratch space `scr` at
`r15` and the `len` bytes of blocks `src` at `rsi` do not overlap each other
or the return address, and may be accessed. -/
structure CallOkN (P : Params) (s : State) (st scr src : Addr) (len : Nat) : Prop where
  rbx : s.gpr .rbx = st
  r15 : s.gpr .r15 = scr
  rsi : s.gpr .rsi = src
  d₁ : Region.Disjoint ⟨st, P.N⟩ ⟨scr, P.so⟩
  d₂ : Region.Disjoint ⟨src, len⟩ ⟨st, P.N⟩
  d₃ : Region.Disjoint ⟨src, len⟩ ⟨scr, P.so⟩
  d₄ : (below (s.gpr .rsp) 8).Disjoint ⟨st, P.N⟩
  d₅ : (below (s.gpr .rsp) 8).Disjoint ⟨scr, P.so⟩
  d₆ : (below (s.gpr .rsp) 8).Disjoint ⟨src, len⟩
  hc : Covers [⟨src, len⟩, ⟨st, P.N⟩, ⟨scr, P.so⟩] (s.rd ++ s.wr)
  hw : Covers [⟨st, P.N⟩, ⟨scr, P.so⟩] s.wr

/-- For one block (`compressAt`). -/
abbrev CallOk (P : Params) (s : State) (st scr src : Addr) : Prop := CallOkN P s st scr src P.B

/-- The arguments of the call, set up from `σ`, with `n` blocks. -/
structure Setup (σ s : State) (n : BitVec 64) : Prop where
  rdi : s.gpr .rdi = σ.gpr .rbx
  rdx : s.gpr .rdx = n
  rcx : s.gpr .rcx = σ.gpr .r15
  rsi : s.gpr .rsi = σ.gpr .rsi
  cs : ∀ r ∈ calleeSaved, s.gpr r = σ.gpr r
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mem : s.mem = σ.mem

/-- The instruction setting the number of blocks, and what it sets. -/
def SetsN (i : Instr) (N : State → BitVec 64) : Prop :=
  ∀ s, WP isa (.block [.mov .rdi (.reg .rbx), i, .mov .rcx (.reg .r15)]) s fun s' => Setup s s' (N s)

theorem setsN_one : SetsN (.mov32 .rdx (.imm 1)) fun _ => 1 := by
  intro s
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, readSrc32, isa, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by simp [State.setReg, State.setReg32], by simp [State.setReg, State.setReg32],
    by simp [State.setReg, State.setReg32], by simp [State.setReg, State.setReg32],
    fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [State.setReg, State.setReg32]

theorem setsN_r14 : SetsN (.mov .rdx (.reg .r14)) fun s => s.gpr .r14 := by
  intro s
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, isa, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by simp [State.setReg], by simp [State.setReg],
    by simp [State.setReg], by simp [State.setReg],
    fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [State.setReg]

section
variable {P : Params} (H : Md P.B P.N P.L)

/-- The call's precondition, narrowed to the regions it is given. -/
theorem call_hyps {σ s : State} {st scr src : Addr} {k : Nat} {n : BitVec 64} (hk : n.toNat = k)
    (h : CallOkN P σ st scr src (P.B * k)) (hs : Setup σ s n) :
    (compressK H).pre (s.callEntry.withRegions [⟨src, P.B * k⟩] [⟨st, P.N⟩, ⟨scr, P.so⟩]) ∧
    Covers ([⟨src, P.B * k⟩] ++ [⟨st, P.N⟩, ⟨scr, P.so⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨st, P.N⟩, ⟨scr, P.so⟩] s.wr := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := hs.cs _ (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine ⟨?_, ?_, ?_⟩
  · simp only [compressK, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp),
      hne _ (by decide : Reg.rcx ≠ .rsp), hs.rdi, hs.rdx, hs.rcx, hs.rsi, h.rbx, h.r15, h.rsi, hsp, hk]
    exact ⟨by simp, by simp, h.d₁, by simpa using h.d₂, by simpa using h.d₃, h.d₄, h.d₅⟩
  · rw [hs.rd, hs.wr]; simpa using h.hc
  · rw [hs.wr]; exact h.hw

/-- Compressing the `k` blocks at `rsi` into the hash value at `rbx`, with
scratch space at `r15`, by calling the compression function, when `i` sets
`rdx` to `k`. -/
theorem compressWith_ok {i : Instr} {N : State → BitVec 64} (hi : SetsN i N) {name : String}
    {code : Prog isa} (hf : CalleeOk H code) {s : State} {st scr src : Addr} {k : Nat} (hk : (N s).toNat = k)
    (h : CallOkN P s st scr src (P.B * k)) (hB : P.B * k ≤ 2 ^ 64) (hN : P.N ≤ 2 ^ 64)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, P.N⟩, ⟨scr, P.so⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      H.stateAt s'.mem st = H.compressBlocks (H.stateAt s.mem st) s.mem src k →
      s'.gpr .rdi = st → s'.gpr .rcx = scr → Q s') :
    WP isa (compressWith i name code) s Q := by
  unfold compressWith
  refine WP.seq (WP.mono (hi s) fun s₁ hs => ?_)
  have e₁ : s₁.gpr .rdi = st := hs.rdi.trans h.rbx
  have e₂ := hs.rdx
  have e₃ : s₁.gpr .rcx = scr := hs.rcx.trans h.r15
  have e₄ : s₁.gpr .rsi = src := hs.rsi.trans h.rsi
  have e₅ := hs.cs
  have hsp : s₁.gpr .rsp = s.gpr .rsp := e₅ _ (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  obtain ⟨hpre, hc, hw⟩ := call_hyps H hk h hs
  refine WP.seq (WP.call (k := compressK H) hf.verified hf.nosp (by rw [hf.depth]; decide)
    (rd := [⟨src, P.B * k⟩]) (wr := [⟨st, P.N⟩, ⟨scr, P.so⟩]) hpre hc hw ?_)
  intro s₂ hrd hwr hcs hfr hkeep ⟨s₃, hm₃, _, hpost⟩
  have k₁ := hkeep .rdi hf.keeps_rdi
  have k₃ := hkeep .rcx hf.keeps_rcx
  simp only [compressK, State.withRegions_gpr, State.withRegions_mem,
    hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
    hne _ (by decide : Reg.rdx ≠ .rsp), e₁, e₂, e₄, hm₃, hk] at hpost
  have hst : H.stateAt s₁.callEntry.mem st = H.stateAt s.mem st :=
    (H.stateAt_congr fun i hi => callEntry_byte s₁ (R := ⟨st, P.N⟩) (by rw [hsp]; exact h.d₄)
      hN hi).trans (by rw [hs.mem])
  have hblk : H.compressBlocks (H.stateAt s.mem st) s₁.callEntry.mem src k =
      H.compressBlocks (H.stateAt s.mem st) s.mem src k := by
    apply H.compressBlocks_congr
    intro j hj
    rw [callEntry_byte s₁ (R := ⟨src, P.B * k⟩) (by rw [hsp]; exact h.d₆) hB hj, hs.mem]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, isa, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine hQ _ (hrd.trans hs.rd) (hwr.trans hs.wr) (fun r hr => ?_) (by
    rw [hf.depth, hsp, hs.mem] at hfr; simpa [State.setReg] using hfr)
    (by simp only [State.setReg]; rw [hpost, hst, hblk]) (by simp [State.setReg, k₁, e₁])
    (by simp [State.setReg, k₃, e₃])
  have h₂ := hcs r hr
  simp only [State.setReg]
  by_cases h15 : r = .r15
  · subst h15; simp [k₃, e₃, h.r15]
  · by_cases hbx : r = .rbx
    · subst hbx; simp [k₁, e₁, h.rbx]
    · simp [h15, hbx, h₂, e₅ r hr]

/-- Compressing the block at `rsi` into the hash value at `rbx`, with scratch
space at `r15`, by calling the compression function. -/
theorem compressAt_ok {name : String} {code : Prog isa} (hf : CalleeOk H code) {s : State}
    {st scr src : Addr} (h : CallOk P s st scr src) (hB : P.B ≤ 2 ^ 64) (hN : P.N ≤ 2 ^ 64)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, P.N⟩, ⟨scr, P.so⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      H.stateAt s'.mem st = H.compress (H.stateAt s.mem st) (H.blockAt s.mem src) →
      s'.gpr .rdi = st → s'.gpr .rcx = scr → Q s') :
    WP isa (compressAt name code) s Q :=
  compressWith_ok H setsN_one hf (k := 1) rfl (by rw [Nat.mul_one]; exact h) (by rw [Nat.mul_one]; exact hB) hN
    fun s' h₁ h₂ h₃ h₄ h₅ => hQ s' h₁ h₂ h₃ h₄ (by rw [h₅, Md.compressBlocks_one])

/-- `compressWith` is constant time, in runs that agree on its arguments. -/
theorem compressWith_rel {i : Instr} {N : State → BitVec 64} (hi : SetsN i N)
    (hti : ∃ hc, (taint.check (X86_64.Taint.ofRegs []) (.block [.mov .rdi (.reg .rbx), i, .mov .rcx (.reg .r15)])
      hc).isSome = true)
    {name : String} {code : Prog isa} (hf : CalleeOk H code) {P' : State → State → Prop}
    (hP : ∀ s₁ s₂, P' s₁ s₂ → (∃ a b c k, (N s₁).toNat = k ∧ CallOkN P s₁ a b c (P.B * k)) ∧
      (∃ a b c k, (N s₂).toNat = k ∧ CallOkN P s₂ a b c (P.B * k)) ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .r15 = s₂.gpr .r15 ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rsp = s₂.gpr .rsp ∧ N s₁ = N s₂) :
    RelCT isa P' (compressWith i name code) fun _ _ => True := by
  unfold compressWith
  obtain ⟨_, hti⟩ := hti
  have su := (RelCT.taint (A := taint) (P := P') (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov .rdi (.reg .rbx), i, .mov .rcx (.reg .r15)]) hti).wpDep
      (F := fun σ s => Setup σ s (N σ)) fun s₁ s₂ _ => ⟨hi s₁, hi s₂⟩
  have cl := RelCT.callEx (n := name) (k := compressK H)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P' σ₁ σ₂ ∧ Setup σ₁ s₁ (N σ₁) ∧ Setup σ₂ s₂ (N σ₂)) hf.verified hf.ct
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨⟨_, _, _, _, hk₁, k₁⟩, ⟨_, _, _, _, hk₂, k₂⟩, ebx, e15, esi, esp, eN⟩ := hP _ _ hp
      obtain ⟨p₁, c₁, w₁⟩ := call_hyps H hk₁ k₁ h₁
      obtain ⟨p₂, c₂, w₂⟩ := call_hyps H hk₂ k₂ h₂
      refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, ?_⟩
      · simp only [compressK, State.withRegions_gpr,
          State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp)]
        exact ⟨by rw [h₁.rdi, h₂.rdi, ebx], by rw [h₁.rsi, h₂.rsi, esi], by rw [h₁.rdx, h₂.rdx, eN],
          by rw [h₁.rcx, h₂.rcx, e15]⟩
      · rw [h₁.cs _ (by simp [calleeSaved]), h₂.cs _ (by simp [calleeSaved]), esp]
  have tl := RelCT.taint (A := taint) (P := fun _ _ => True) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx)])
    (by taint_decide)
  exact su.seq (cl.seq tl)

/-- `compressAt` is constant time, in runs that agree on its arguments. -/
theorem compressAt_rel {name : String} {code : Prog isa} (hf : CalleeOk H code) {P' : State → State → Prop}
    (hP : ∀ s₁ s₂, P' s₁ s₂ → (∃ a b c, CallOk P s₁ a b c) ∧ (∃ a b c, CallOk P s₂ a b c) ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .r15 = s₂.gpr .r15 ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P' (compressAt name code) fun _ _ => True :=
  compressWith_rel H setsN_one ⟨_, by taint_decide⟩ hf fun s₁ s₂ hp =>
    let ⟨⟨a, b, c, h₁⟩, ⟨a', b', c', h₂⟩, e⟩ := hP s₁ s₂ hp
    ⟨⟨a, b, c, 1, rfl, by rw [Nat.mul_one]; exact h₁⟩, ⟨a', b', c', 1, rfl, by rw [Nat.mul_one]; exact h₂⟩,
      e.1, e.2.1, e.2.2.1, e.2.2.2, rfl⟩

end

/-! ## One instruction at a time

Weakest-precondition rules for the instruction forms used here, exposing
only what changes, so that proofs about a block stay small. -/

/-- `s'` is `s` with register `d` set to `v` (flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) {w : Nat} (d : Reg) (x : BitVec w) (c o : Bool) (v : BitVec 64) :
    Upd s ((arithFlags s x c o).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → s'.zf = s.zf → s'.cf = s.cf →
    WP isa (.block is) s' Q) : WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

theorem wp_mov32i {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (v.setWidth 64) → s'.zf = s.zf →
    s'.cf = s.cf → WP isa (.block is) s' Q) : WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

theorem wp_addi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v.signExtend 64) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_sub {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d - s.gpr r) → s'.zf = some (s.gpr d - s.gpr r == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_add {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d + s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_mov32m {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem.readW a 32).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc32, State.load32, State.setReg32, ha, hin]

theorem wp_bswap32 {d : Reg}
    (k : ∀ s', Upd s s' d ((bswap32 ((s.gpr d).setWidth 32)).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap32 d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_store32 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 32) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store32 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 32) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store32, ha, hout]

theorem wp_movm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' d (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d (s.mem.readW a 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc, State.load64, ha, hin]

theorem wp_andi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_shr {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  refine WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some ((s.gpr d >>> n) == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ?_)
  · simp [exec, execShift, hn]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h]; rfl, rfl, rfl, rfl⟩

/-- `cmp d, r`: CF is `d < r` (unsigned). -/
theorem wp_cmp {d r : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      s'.zf = some (s.gpr d - s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (v.signExtend 64).toNat)) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

theorem wp_test {d : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl)

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' d ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 8) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 8) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store8, ha, hout]

theorem wp_store {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a (s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store64, ha, hout]

theorem wp_bswap {d : Reg}
    (k : ∀ s', Upd s s' d (bswap64 (s.gpr d)) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

end

/-- `test r, r`, as a block of its own. -/
theorem test_ok {s : State} (r : Reg) :
    WP isa (.block [.alu .test r (.reg r)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.zf = some (s.gpr r &&& s.gpr r == 0) :=
  wp_test fun _ g m rd wr z => WP.block_nil ⟨g, m, rd, wr, z⟩

theorem WP.seq_assoc {M : ISA} {a b c : Prog M} {s : M.State} {Q : M.State → Prop} :
    WP M (.seq (.seq a b) c) s Q ↔ WP M (.seq a (.seq b c)) s Q := by
  simp only [WP.seq_iff]

end VG.Proof.MdStream.X86_64
