import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Impl.Pbkdf2.X86_64

/-!
# PBKDF2-HMAC's iteration on x86-64: copying words

Untrusted: everything here is checked by Lean. What `n` copies of a 32-bit
word (`cp32`, `Impl/Pbkdf2/X86_64.lean`) write.
-/

namespace VG.Proof.Pbkdf2.X86_64

open VG VG.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.X86_64 (cp32)
open VG.Proof.MdStream.X86_64 (ea_at ofInt_natCast wp_mov32m wp_store32)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Hmac.Common (copy_mem bytesAt_zero)
open VG.Spec.Sha256 (bytesAt)

theorem ea_off (s : State) (b : Reg) (o j : Nat) :
    s.ea (at_ b (o + j)) = s.gpr b + BitVec.ofNat 64 o + BitVec.ofNat 64 j := by
  rw [ea_at, ofInt_natCast, BitVec.ofNat_add, BitVec.add_assoc]

/-- `n` copies of 32-bit words write the `4 n` bytes at `src + o₁` to `dst + o₂`. -/
theorem copy32_ok {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) (o₁ o₂ : Nat) (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (4 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (4 * n) →
    4 * n < 2 ^ 64 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (4 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp32 src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep hlt k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [cp32, List.cons_append, List.nil_append]
    refine wp_mov32m (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, g₁ _ hs]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_store32 (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, u₂.other _ hd, g₁ _ hd]) (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ g₃ m₃ rd₃ wr₃ => k s₃ (fun r hr => by rw [g₃, u₂.other r hr, g₁ r hr])
        (by rw [rd₃, u₂.rd, rd₁]) (by rw [wr₃, u₂.wr, wr₁]) ?_
    rw [m₃, u₂.gpr, u₂.mem, m₁, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      Nat.mul_succ]
    exact copy_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) (by omega)

end VG.Proof.Pbkdf2.X86_64
