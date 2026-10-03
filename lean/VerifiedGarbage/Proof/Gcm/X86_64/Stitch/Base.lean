import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Ghash
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32

/-!
# Interleaved counter mode and GHASH: the setting

The interleaved loops (`Impl.Gcm.X86_64.Stitch`) start from a state `s₀`
whose registers hold the key context (`rdi`), the number of rounds (`rsi`),
the counter (`rdx`), `Y` (`rcx`), the data (`r8`), the number of blocks
(`r9`, a multiple of 16) and the working space (`r11`). `SPre s₀` is what
they need of it: the regions they read and write are accessible, disjoint
where one is written, and do not wrap around.
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom)

/-! ## Accesses within the regions -/

theorem ofNat_toNat_le (off : Nat) : (BitVec.ofNat 64 off).toNat ≤ off := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _

/-- `n` bytes at `off` from the start of an accessible run of `L ≥ off + n`
bytes are accessible. -/
theorem in_sub {rs : List Region} {b : Addr} {L off n : Nat} (h : InRegions rs b L)
    (ho : off + n ≤ L) : InRegions rs (b + BitVec.ofNat 64 off) n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  unfold Region.Contains at *
  have e : b + BitVec.ofNat 64 off - r.base = (b - r.base) + BitVec.ofNat 64 off := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 off),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add]
  have := Nat.mod_le ((b - r.base).toNat + (BitVec.ofNat 64 off).toNat) (2 ^ 64)
  have := ofNat_toNat_le off
  omega

theorem in_sub_int {rs : List Region} {b : Addr} {L off n : Nat} (h : InRegions rs b L)
    (ho : off + n ≤ L) : InRegions rs (b + BitVec.ofInt 64 (off : Int)) n := by
  rw [show BitVec.ofInt 64 (off : Int) = BitVec.ofNat 64 off from BitVec.ofInt_natCast ..]
  exact in_sub h ho

theorem in_rdwr {rs rs' : List Region} {a : Addr} {n : Nat} (h : InRegions rs' a n) :
    InRegions (rs ++ rs') a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

end VG.Proof.Gcm.X86_64.Stitch
