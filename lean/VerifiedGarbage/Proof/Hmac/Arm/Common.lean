import VerifiedGarbage.Proof.Sha256.Arm.Stream.Finalize
import VerifiedGarbage.Proof.Hmac.X86_64.Common
import VerifiedGarbage.Impl.Hmac.Arm

/-!
# HMAC-SHA-256 on ARMv7: common lemmas

Untrusted: everything here is checked by Lean. Words copied between memory
regions; the memory lemmas themselves are target-independent and shared with
x86-64 (`VG.Proof.Hmac.X86_64`).
-/

namespace VG.Proof.Hmac.Arm
open VG VG.Arm
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Hmac.X86_64 (copy_mem)
open VG.Spec.Sha256 (bytesAt)
open VG.Impl.Hmac.Arm (cp)
open VG.Proof.Sha256.Arm.Stream (Upd Mupd wp_ldr wp_str)

theorem add_off (p : Addr) (o j : Nat) :
    p + BitVec.ofNat 64 (o + j) = p + BitVec.ofNat 64 o + BitVec.ofNat 64 j := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- Copying `n` words from `[src + o₁]` to `[dst + o₂]`, through `t`. -/
theorem copy_ok {t src dst : Reg} (hs : src ≠ t) (hd : dst ≠ t) (o₁ o₂ : Nat) (n : Nat)
    (hb : o₁ + 4 * n ≤ 4096 ∧ o₂ + 4 * n ≤ 4096) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (s.gpr src).toNat + o₁ + 4 * n ≤ 2 ^ 32 → (s.gpr dst).toNat + o₂ + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr src) + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (State.addr (s.gpr src) + BitVec.ofNat 64 o₁) (4 * n)
      (State.addr (s.gpr dst) + BitVec.ofNat 64 o₂) (4 * n) →
    (∀ s', (∀ r, r ≠ t → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr (s.gpr dst) + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (State.addr (s.gpr src) + BitVec.ofNat 64 o₁) (4 * n)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp t src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl
      (by rw [Nat.mul_zero, VG.Proof.Hmac.X86_64.bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q fs fd hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih ⟨by omega, by omega⟩ _ s Q (by omega) (by omega) (fun j hj => hin j (by omega))
      (fun j hj => hout j (by omega)) (fun x hx hy => hsep x (by omega) (by omega))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [cp, List.cons_append, List.nil_append]
    refine wp_ldr (a := State.addr (s.gpr src) + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n))
      (by omega) (by rw [g₁ _ hs, addr_add (by omega), add_off])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_str (a := State.addr (s.gpr dst) + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * n))
      (by omega) (by rw [u₂.other _ hd, g₁ _ hd, addr_add (by omega), add_off])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ u₃ => k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) (by rw [u₃.sp, u₂.sp, sp₁]) ?_
    rw [u₃.mem, u₂.gpr, u₂.mem, m₁, Nat.mul_succ]
    exact copy_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) (by omega)

end VG.Proof.Hmac.Arm
