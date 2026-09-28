import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Finalize
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Impl.Hmac.PPC64LE

/-!
# HMAC-SHA-256 on PPC64LE: common lemmas

Untrusted: everything here is checked by Lean. Words copied between memory
regions; the memory lemmas themselves are target-independent and shared with
the other targets (`VG.Proof.Hmac.Common`).
-/

namespace VG.Proof.Hmac.PPC64LE
open VG VG.PPC64LE
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Hmac.Common (copy_mem)
open VG.Spec.Sha256 (bytesAt)
open VG.Impl.Hmac.PPC64LE (cp32 cp64)
open VG.Proof.Sha256.PPC64LE.Stream (Upd Mupd wp_lwz wp_stw wp_ld wp_std)

theorem add_off (p : Addr) (o j : Nat) :
    p + BitVec.ofNat 64 (o + j) = p + BitVec.ofNat 64 o + BitVec.ofNat 64 j := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem copy32_ok {src dst : Reg} (hs : src ≠ .r8) (hd : dst ≠ .r8) (hs0 : src ≠ .r0) (hd0 : dst ≠ .r0) (o₁ o₂ : Nat) (n : Nat)
    (ho : o₁ % 4 = 0 ∧ o₂ % 4 = 0) (hb : o₁ + 4 * n ≤ 2 ^ 15 ∧ o₂ + 4 * n ≤ 2 ^ 15) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (4 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (4 * n) →
    (∀ s', (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (4 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp32 src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by rw [Nat.mul_zero, VG.Proof.Hmac.Common.bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih ⟨by omega, by omega⟩ _ s Q (fun j hj => hin j (by omega))
      (fun j hj => hout j (by omega)) (fun x hx hy => hsep x (by omega) (by omega))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [cp32, List.cons_append, List.nil_append]
    refine wp_lwz (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n)) hs0
      (by omega) (by rw [g₁ _ hs, add_off]) (by rw [rd₁, wr₁]; exact hin n (by omega))
      fun s₂ u₂ => ?_
    refine wp_stw (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * n)) hd0
      (by omega) (by rw [u₂.other _ hd, g₁ _ hd, add_off])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ u₃ => k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) (by rw [u₃.sp, u₂.sp, sp₁]) ?_
    rw [u₃.mem, u₂.gpr, u₂.mem, m₁, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      Nat.mul_succ]
    exact copy_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) (by omega)

theorem copy64_ok {src dst : Reg} (hs : src ≠ .r8) (hd : dst ≠ .r8) (hs0 : src ≠ .r0) (hd0 : dst ≠ .r0) (o₁ o₂ : Nat) (n : Nat)
    (ho : o₁ % 8 = 0 ∧ o₂ % 8 = 0) (hb : o₁ + 8 * n ≤ 2 ^ 15 ∧ o₂ + 8 * n ≤ 2 ^ 15) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (8 * k)) 8) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (8 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (8 * n) →
    (∀ s', (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (8 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp64 src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by rw [Nat.mul_zero, VG.Proof.Hmac.Common.bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih ⟨by omega, by omega⟩ _ s Q (fun j hj => hin j (by omega))
      (fun j hj => hout j (by omega)) (fun x hx hy => hsep x (by omega) (by omega))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [cp64, List.cons_append, List.nil_append]
    refine wp_ld (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (8 * n)) hs0
      ⟨by omega, by omega⟩ (by rw [g₁ _ hs, add_off]) (by rw [rd₁, wr₁]; exact hin n (by omega))
      fun s₂ u₂ => ?_
    refine wp_std (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (8 * n)) hd0
      ⟨by omega, by omega⟩ (by rw [u₂.other _ hd, g₁ _ hd, add_off])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ u₃ => k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) (by rw [u₃.sp, u₂.sp, sp₁]) ?_
    rw [u₃.mem, u₂.gpr, u₂.mem, m₁, Nat.mul_succ]
    exact copy_mem s.mem _ _ n 8 (by rwa [← Nat.mul_succ]) (by omega)

end VG.Proof.Hmac.PPC64LE
