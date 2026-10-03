import VerifiedGarbage.Proof.Weierstrass.X86_64.Ladder
import VerifiedGarbage.Proof.Weierstrass.X86_64.Flags
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.X86_64.Spill

/-!
# ECDSA on x86-64: the curve, the arguments and the working space

What the proof of `Impl.Ecdsa.X86_64.Cfg.sign` needs of a curve (`CfgOk`)
and of its arguments (`Pre`), for any curve of `n` words, and the state
`setup` leaves (`SetupPost`).

The working space is the `8192` bytes at `scratch`: the saved registers in
`[0, 48)`, the slots `c.sl i = 64 + 8 n i` of `n` words for `i < nslots`, and
the tables of bits `bitsAt n j` (`64 n` bytes each, `j < 3`), which are
slots `nslots + 8 j` to `nslots + 8 j + 7`.
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

/-- The size of the working space, in bytes. -/
abbrev size : Nat := 8192

/-- What the proof needs of a curve: its field and order are odd and fit in
`n` words (`n < 7`), the field is prime and the curve has no point of order 2
(`Good`), `p < 2n` (so `x mod n` is one conditional subtraction), the
Montgomery constants are right, encodings are `8 n` bytes, and a hash of
`8 n` bytes is not truncated. `n ≤ 4`: the code keeps `out` in `r14`, which
the multiplications of more words use. -/
structure CfgOk (c : Cfg) : Prop where
  n0 : 0 < c.n
  n7 : c.n < 7
  n4 : c.n ≤ 4
  good : Good c.C
  onG : onCurve c.C (G c.C) = true
  p_odd : c.C.p % 2 = 1
  n_odd : c.C.n % 2 = 1
  p_lt : c.C.p < 2 ^ (64 * c.n)
  n_lt : c.C.n < 2 ^ (64 * c.n)
  p_ge : 3 ≤ c.C.p
  n_ge : 3 ≤ c.C.n
  p_lt_2n : c.C.p < 2 * c.C.n
  minv_p : (c.C.p * (BitVec.ofNat 64 (minv c.C.p)).toNat + 1) % 2 ^ 64 = 0
  minv_n : (c.C.n * (BitVec.ofNat 64 (minv c.C.n)).toNat + 1) % 2 ^ 64 = 0
  len : c.C.len = 8 * c.n
  hash : 64 * c.n ≤ Spec.Ecdsa.nBits c.C

/-- The arguments: `out = rdi` (`16 n` bytes), `d = rsi`, `digest = rdx`,
`k = rcx` (`8 n` bytes each) and `scratch = r8`, readable and writable as
the contract says and apart from each other as it says. -/
structure Pre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rsi, 8 * c.n⟩, ⟨s.gpr .rdx, 8 * c.n⟩, ⟨s.gpr .rcx, 8 * c.n⟩]
  wr : s.wr = [⟨s.gpr .rdi, 16 * c.n⟩, ⟨s.gpr .r8, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .rdi, 16 * c.n⟩ ⟨s.gpr .r8, size⟩
  out_d : Region.Disjoint ⟨s.gpr .rdi, 16 * c.n⟩ ⟨s.gpr .rsi, 8 * c.n⟩
  out_digest : Region.Disjoint ⟨s.gpr .rdi, 16 * c.n⟩ ⟨s.gpr .rdx, 8 * c.n⟩
  out_k : Region.Disjoint ⟨s.gpr .rdi, 16 * c.n⟩ ⟨s.gpr .rcx, 8 * c.n⟩
  d_sc : Region.Disjoint ⟨s.gpr .rsi, 8 * c.n⟩ ⟨s.gpr .r8, size⟩
  digest_sc : Region.Disjoint ⟨s.gpr .rdx, 8 * c.n⟩ ⟨s.gpr .r8, size⟩
  k_sc : Region.Disjoint ⟨s.gpr .rcx, 8 * c.n⟩ ⟨s.gpr .r8, size⟩
  out_fit : (s.gpr .rdi).toNat + 16 * c.n ≤ 2 ^ 64
  sc_fit : (s.gpr .r8).toNat + size ≤ 2 ^ 64

/-- What `setup` needs of its arguments (`Pre` gives it, and so can the
arguments of other functions that run it): the working space `scratch = r8`
writable, and `k = rcx`, `d = rsi` and `digest = rdx` (`8 n` bytes each)
readable and apart from it. -/
structure SetupPre (c : Cfg) (s : State) : Prop where
  wr : (⟨s.gpr .r8, size⟩ : Region) ∈ s.wr
  k_in : ∀ e, e + 8 ≤ 8 * c.n → InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 e) 8
  d_in : ∀ e, e + 8 ≤ 8 * c.n → InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 e) 8
  digest_in : ∀ e, e + 8 ≤ 8 * c.n → InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 e) 8
  d_sc : Region.Disjoint ⟨s.gpr .rsi, 8 * c.n⟩ ⟨s.gpr .r8, size⟩
  digest_sc : Region.Disjoint ⟨s.gpr .rdx, 8 * c.n⟩ ⟨s.gpr .r8, size⟩
  k_sc : Region.Disjoint ⟨s.gpr .rcx, 8 * c.n⟩ ⟨s.gpr .r8, size⟩
  sc_fit : (s.gpr .r8).toNat + size ≤ 2 ^ 64

theorem Pre.setup {c : Cfg} {s : State} (hp : Pre c s) (h7 : c.n < 7) : SetupPre c s where
  wr := by rw [hp.wr]; simp
  k_in := inRegions_words (by rw [hp.rd]; simp) (by omega)
  d_in := inRegions_words (by rw [hp.rd]; simp) (by omega)
  digest_in := inRegions_words (by rw [hp.rd]; simp) (by omega)
  d_sc := hp.d_sc
  digest_sc := hp.digest_sc
  k_sc := hp.k_sc
  sc_fit := hp.sc_fit

/-- The number in slot `i`. -/
abbrev sv (c : Cfg) (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (c.sl i) c.n

/-- What `setup` leaves, from the state `s₀` at entry, with the working space
at `base = r8`: `rdi = base`, `out` in `r14`, the callee-saved registers in
`[0, 48)`, `k`, `d` and the hash in their slots, the constants in theirs,
and the flag all ones; only `rax`, `rdi` and `r14` and the working space
changed. -/
structure SetupPost (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  r14 : s.gpr .r14 = s₀.gpr .rdi
  keep : KeepRegs [.rax, .rdi, .r14] s₀ s
  unch : Unch base [(0, size)] s₀.mem s.mem
  saved : Spill.Saved s.mem base s₀.gpr Cfg.saved
  k : sv c base s K = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rcx) (8 * c.n))
  d : sv c base s D = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rsi) (8 * c.n))
  e : sv c base s E = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (8 * c.n))
  consts : ∀ ix ∈ c.consts, sv c base s ix.1 = ix.2
  flag : word s.mem base (c.sl FLAG) = BitVec.allOnes 64

/-! ## Slots -/

theorem sl_eq (c : Cfg) (i : Nat) : c.sl i = 64 + 8 * c.n * i := rfl

theorem bitsAt_eq (c : Cfg) (j : Nat) : bitsAt c.n j = 64 + 8 * c.n * 45 + 64 * c.n * j := rfl

/-- Slots `i < j` are apart. -/
theorem sl_lt (c : Cfg) {i j : Nat} (h : i < j) : c.sl i + 8 * c.n ≤ c.sl j := by
  rw [sl_eq, sl_eq]
  have := Nat.mul_le_mul_left (8 * c.n) h
  rw [Nat.mul_succ] at this
  omega

theorem sl_apart (c : Cfg) {i j : Nat} (h : i ≠ j) :
    c.sl i + 8 * c.n ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact Or.inl (sl_lt c h)
  · exact Or.inr (sl_lt c h)

theorem sl_inj (c : Cfg) (hn : 0 < c.n) {i j : Nat} (h : c.sl i = c.sl j) : i = j := by
  by_contra hij
  have := sl_apart c hij
  omega

/-- Every slot and table is in the working space. -/
theorem sl_le (c : Cfg) (hn : c.n < 7) {i : Nat} (hi : i < 45) : c.sl i + 8 * c.n ≤ size := by
  rw [sl_eq]
  have := Nat.mul_le_mul_left (8 * c.n) hi
  rw [Nat.mul_succ] at this
  have : 8 * c.n * 45 ≤ 8 * 6 * 45 := Nat.mul_le_mul_right _ (by omega)
  show _ ≤ 8192
  omega

theorem bitsAt_le (c : Cfg) (hn : c.n < 7) {j : Nat} (hj : j < 3) : bitsAt c.n j + 64 * c.n ≤ size := by
  rw [bitsAt_eq]
  have := Nat.mul_le_mul_left (64 * c.n) hj
  rw [Nat.mul_succ] at this
  show _ ≤ 8192
  omega

end VG.Proof.Ecdsa.X86_64
