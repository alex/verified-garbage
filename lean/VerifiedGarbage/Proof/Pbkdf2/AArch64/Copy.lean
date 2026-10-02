import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Impl.Pbkdf2.AArch64

/-!
# PBKDF2-HMAC's iteration on AArch64: copying words

What `n` copies of a 32-bit word (`cp32`, `Impl/Pbkdf2/AArch64.lean`) write.
-/

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64
open VG.Impl.Pbkdf2.AArch64 (cp32)
open VG.Proof.MdStream.AArch64 (wp_ldr32 wp_str32 add_ofNat)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Hmac.Common (copy_mem bytesAt_zero)
open VG.Spec.Sha256 (bytesAt)

/-- `n` copies of 32-bit words write the `4 n` bytes at `src + o₁` to `dst + o₂`. -/
theorem copy32_ok {src dst : Reg} (hs : src ≠ .x9) (hd : dst ≠ .x9) (o₁ o₂ : Nat) (n : Nat)
    (h₁ : o₁ % 4 = 0 ∧ o₁ + 4 * n ≤ 4096 * 4) (h₂ : o₂ % 4 = 0 ∧ o₂ + 4 * n ≤ 4096 * 4) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (4 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (4 * n) →
    (∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (4 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp32 src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih ⟨h₁.1, by omega⟩ ⟨h₂.1, by omega⟩ _ s Q (fun j hj => hin j (by omega))
      (fun j hj => hout j (by omega)) (fun x hx hy => hsep x (by omega) (by omega))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [cp32, List.cons_append, List.nil_append]
    refine wp_ldr32 (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [g₁ _ hs, add_ofNat]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_str32 (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [u₂.other _ hd, g₁ _ hd, add_ofNat]) (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ g₃ => k s₃ (fun r hr => by rw [g₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [g₃.rd, u₂.rd, rd₁]) (by rw [g₃.wr, u₂.wr, wr₁]) (by rw [g₃.sp, u₂.sp, sp₁]) ?_
    have hlt : 4 * n + 4 < 2 ^ 64 := by omega
    rw [g₃.mem, u₂.gpr, u₂.mem, m₁, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      Nat.mul_succ]
    exact copy_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) hlt

end VG.Proof.Pbkdf2.AArch64
