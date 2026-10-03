import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
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

section
variable (s₀ : State)

/-- The key context: the key schedule, and the hash subkey at `+ 240`. -/
abbrev kp : Addr := s₀.gpr .rdi
abbrev nr : Nat := (s₀.gpr .rsi).toNat
abbrev cp : Addr := s₀.gpr .rdx
abbrev yp : Addr := s₀.gpr .rcx
abbrev dp : Addr := s₀.gpr .r8
abbrev nb : Nat := (s₀.gpr .r9).toNat
/-- The working space: the powers. -/
abbrev pp : Addr := s₀.gpr .r11
abbrev kR : Region := ⟨kp s₀, 256⟩
abbrev cR : Region := ⟨cp s₀, 16⟩
abbrev yR : Region := ⟨yp s₀, 16⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev pR : Region := ⟨pp s₀, 256⟩
/-- The key schedule, and `CIPH_K`. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem (kp s₀) (16 * (nr s₀ + 1))
abbrev ciph : Block → Block := aesWith (nr s₀) (sch s₀)
abbrev cb : Block := blockAt s₀.mem (cp s₀)
/-- The hash subkey, and `Y`. -/
abbrev hk : Block := blockAt s₀.mem (kp s₀ + 240)
abbrev y₀ : Block := blockAt s₀.mem (yp s₀)
/-- Block `k` of the data, where it starts, and encrypted. -/
abbrev bAddr (k : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * k)
abbrev blk (k : Nat) : Block := blockAt s₀.mem (bAddr s₀ k)
abbrev ctb (k : Nat) : Block := blk s₀ k ^^^ ciph s₀ (Nat.repeat inc32 k (cb s₀))

end

structure SPre (s₀ : State) : Prop where
  rounds : nr s₀ = 10 ∨ nr s₀ = 12 ∨ nr s₀ = 14
  nb16 : 16 ≤ nb s₀
  nbm : nb s₀ % 16 = 0
  k_in : InRegions (s₀.rd ++ s₀.wr) (kp s₀) 256
  c_in : InRegions s₀.wr (cp s₀) 16
  y_in : InRegions s₀.wr (yp s₀) 16
  d_in : InRegions s₀.wr (dp s₀) (16 * nb s₀)
  p_in : InRegions s₀.wr (pp s₀) 256
  d_k : (dR s₀).Disjoint (kR s₀)
  d_c : (dR s₀).Disjoint (cR s₀)
  d_y : (dR s₀).Disjoint (yR s₀)
  d_p : (dR s₀).Disjoint (pR s₀)
  p_k : (pR s₀).Disjoint (kR s₀)
  p_c : (pR s₀).Disjoint (cR s₀)
  p_y : (pR s₀).Disjoint (yR s₀)
  c_y : (cR s₀).Disjoint (yR s₀)
  c_k : (cR s₀).Disjoint (kR s₀)
  y_k : (yR s₀).Disjoint (kR s₀)
  wrap_d : (dp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64
  wrap_k : (kp s₀).toNat + 256 ≤ 2 ^ 64
  wrap_p : (pp s₀).toNat + 256 ≤ 2 ^ 64

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
