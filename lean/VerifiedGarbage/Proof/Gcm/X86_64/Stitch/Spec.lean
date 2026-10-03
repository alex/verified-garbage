import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Spec.Gcm

/-!
# Interleaved counter mode and GHASH: what the loops need and do

Untrusted: everything here is checked by Lean. The interleaved loops
(`Impl.Gcm.X86_64.Stitch`) start from a state `s₀` whose registers hold the
key context (`rdi`), the number of rounds (`rsi`), the counter (`rdx`), `Y`
(`rcx`), the data (`r8`), the number of blocks (`r9`, a multiple of 16) and
the working space (`r11`). `SPre s₀` is what they need of it, and `EPost`,
`DPost` what they do (`StitchOk`). This module states them without the
algebra their proofs need (`Proof/Gcm/Poly.lean`), so that the functions
calling the loops are proven for any proof of `StitchOk`, which only the
instances that use the loops import.
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

/-- What the encryption leaves: the data encrypted, the counter advanced, `Y`
continued over the ciphertext, nothing else written but the working space. -/
structure EPost (s₀ s : State) : Prop where
  data : blocksAt s.mem (dp s₀) (nb s₀) = Spec.Gcm.ctr32 (ciph s₀) (cb s₀) (blocksAt s₀.mem (dp s₀) (nb s₀))
  ctr : blockAt s.mem (cp s₀) = Nat.repeat inc32 (nb s₀) (cb s₀)
  y : blockAt s.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s.mem (dp s₀) (nb s₀))
  frame : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem s.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What the decryption leaves: the data decrypted, the counter advanced, `Y`
continued over the blocks as they were, nothing else written but the working
space. -/
structure DPost (s₀ s : State) : Prop where
  data : blocksAt s.mem (dp s₀) (nb s₀) = Spec.Gcm.ctr32 (ciph s₀) (cb s₀) (blocksAt s₀.mem (dp s₀) (nb s₀))
  ctr : blockAt s.mem (cp s₀) = Nat.repeat inc32 (nb s₀) (cb s₀)
  y : blockAt s.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₀.mem (dp s₀) (nb s₀))
  frame : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem s.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The interleaved loops meet their contracts. -/
def StitchOk : Prop :=
  (∀ s₀, SPre s₀ → WP isa Impl.Gcm.X86_64.Stitch.enc s₀ (EPost s₀)) ∧
    (∀ s₀, SPre s₀ → WP isa Impl.Gcm.X86_64.Stitch.dec s₀ (DPost s₀))

end VG.Proof.Gcm.X86_64.Stitch
