import VerifiedGarbage.Proof.Sha3.X86.Call
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# The SHA-3 sponge on x86 (32-bit): common lemmas

Untrusted: everything here is checked by Lean. Facts about bytes, the stack
and the variables `absorb` and `squeeze` keep in their scratch space, which
the proofs of the streaming functions share.
-/

namespace VG.Proof.Sha3.X86.Stream

open VG VG.X86 VG.Impl.Sha3.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.X86.Stream (addr_add_ofNat addr_toNat)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- The low byte of a word in memory is its first byte. -/
theorem low_byte (m : Mem) (a : Addr) : (m.readW a 32).setWidth 8 = m a := by
  have := Mem.readW_byte m a (i := 0) (by omega)
  rw [show a + BitVec.ofNat 64 0 = a by simp] at this
  rw [this]
  ext i hi
  simp

theorem xor_low (b : Byte) (w : BitVec 32) : (b.setWidth 32 ^^^ w).setWidth 8 = b ^^^ w.setWidth 8 := by
  ext i hi; simp

theorem byte_low (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  ext i hi; simp

/-- The contract's stack region. -/
theorem stk_eq {E : BitVec 32} (h : 12 ≤ E.toNat) : below E 12 = ⟨E.setWidth 64 - 12, 12⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

/-- `[x + k]`, where nothing wraps around the 32-bit address space. -/
theorem ptr_addr {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 k) 0 = x.setWidth 64 + BitVec.ofNat 64 k := by
  rw [addr_add_ofNat (by omega), Nat.add_zero]

theorem ofNat_add_one (x : BitVec 32) (k : Nat) :
    x + BitVec.ofNat 32 k + 1 = x + BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

theorem add_sub_self (x y : BitVec 32) : x + y - x = y := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

/-- A part of a region at a 32-bit pointer. -/
theorem sub_word {b : BitVec 32} {N d : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (hd : d + 4 ≤ N) :
    Region.Sub ⟨addr b d, 4⟩ ⟨b.setWidth 64, N⟩ := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [addr_eq (by omega)] at hx
  have hE := addr_toNat b
  generalize b.setWidth 64 = B at *
  bv_omega

/-- Two words of a region at a 32-bit pointer that do not overlap. -/
theorem word_sep {b : BitVec 32} {N d e : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (hd : d + 4 ≤ N)
    (he : e + 4 ≤ N) (h : d + 4 ≤ e ∨ e + 4 ≤ d) (m : Mem) (v : BitVec 32) :
    (m.writeW (addr b e) v).readW (addr b d) 32 = m.readW (addr b d) 32 :=
  VG.Proof.Sha256.X86.Stream.readW_writeW_addr m v (by omega) (by omega) h

/-- A word of the argument area. -/
theorem arg_word {E : BitVec 32} {n d : Nat} (hfit : E.toNat + 4 + n ≤ 2 ^ 32) (hd₁ : 4 ≤ d)
    (hd : d + 4 ≤ n + 4) : Region.Sub ⟨addr E d, 4⟩ ⟨addr E 4, n⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [addr_eq (by omega)] at ha ⊢
  have hE := addr_toNat E
  generalize E.setWidth 64 = b at *
  bv_omega

theorem arg_contains {E : BitVec 32} {n d : Nat} (hfit : E.toNat + 4 + n ≤ 2 ^ 32) (hd₁ : 4 ≤ d)
    (hd : d + 4 ≤ n + 4) : (⟨addr E 4, n⟩ : Region).Contains (addr E d) 4 := by
  simp only [Region.Contains]
  rw [addr_eq (by omega), addr_eq (by omega)]
  have hE := addr_toNat E
  generalize E.setWidth 64 = b at *
  bv_omega

/-- The arguments are above the return address, the stack the calls use below it. -/
theorem arg_stk {E : BitVec 32} {n : Nat} (hfit : E.toNat + 4 + n ≤ 2 ^ 32) (hlo : 12 ≤ E.toNat) :
    Region.Disjoint ⟨addr E 4, n⟩ (below E 12) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [addr_eq (by omega)] at h₁
  rw [Taint.sub_setWidth (by omega)] at h₂
  have hE := addr_toNat E
  generalize E.setWidth 64 = b at *
  bv_omega

theorem ret_stk {E : BitVec 32} (hfit : E.toNat + 4 ≤ 2 ^ 32) (hlo : 12 ≤ E.toNat) :
    Region.Disjoint ⟨E.setWidth 64, 4⟩ (below E 12) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth (by omega)] at h₂
  have hE := addr_toNat E
  generalize E.setWidth 64 = b at *
  bv_omega

theorem argWord_eq {s : State} {n : Nat} (hsp : (s.gpr .esp).toNat + 4 + n ≤ 2 ^ 32) {k : Nat}
    (hk : k < n) :
    addr (s.gpr .esp) 4 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (k / 4))).setWidth 64 = addr (s.gpr .esp) (4 + 4 * (k / 4))
    from rfl, addr_eq (by omega), addr_eq (by omega), BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2; omega

end VG.Proof.Sha3.X86.Stream
