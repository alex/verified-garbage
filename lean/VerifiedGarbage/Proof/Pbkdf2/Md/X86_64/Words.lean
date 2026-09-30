import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Spec.Pbkdf2

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: words

Untrusted: everything here is checked by Lean. What `copy32`
(`Impl/Pbkdf2/Md/X86_64.lean`) writes: 32-bit words copied from one region to
another; and facts about registers and regions the proofs share.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append write_eq_writeBytes)
open VG.Proof.Hmac.Common (copy_mem bytesAt_add bytesAt_writeBytes_sep bytesAt_zero bytesAt_length)
open Spec.Sha256 (bytesAt)

theorem ea_nat (s : State) (b : Reg) (o : Nat) : s.ea (at_ b o) = s.gpr b + BitVec.ofNat 64 o := by
  rw [ea_at, ofInt_natCast]

/-! ## Copies -/

/-- `copy32 src so dst d n` writes the `4 n` bytes at `src + so` to `dst + d`. -/
theorem copy32_ok {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) (o₁ o₂ : Nat) (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (4 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (4 * n) →
    4 * n < 2 ^ 64 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (4 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block (Hash.copy32 src o₁ dst o₂ n ++ rest)) s Q := by
  exact Pbkdf2.X86_64.copy32_ok hs hd o₁ o₂ n

/-! ## Registers and regions -/

theorem wp_mov32r {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem zx32 (x : BitVec 64) : (x.setWidth 32).setWidth 64 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem contains_pre {b : Addr} {n k : Nat} (h : n ≤ k) : (⟨b, k⟩ : Region).Contains b n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

end VG.Proof.Pbkdf2.Md.X86_64
