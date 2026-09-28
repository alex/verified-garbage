import VerifiedGarbage.Proof.Scrypt.X86_64.Common
import VerifiedGarbage.Proof.Md5.AArch64.Stream.Common
import VerifiedGarbage.Impl.Scrypt.AArch64.BlockMix

/-!
# scrypt on AArch64: common lemmas

Untrusted: everything here is checked by Lean. The target-independent lemmas
about addresses and bytes are those of the x86-64 proof
(`Proof/Scrypt/X86_64/Common.lean`); here are the weakest-precondition rules
for the AArch64 forms, and the 64-byte exclusive-or.
-/

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)
open VG.Proof.Md5.AArch64.Stream (Upd Mupd wp_ldr wp_str)
open VG.Proof.Scrypt.X86_64.BlockMix (sub_off writeW_xor xorBytes_length bytesAt_length
  bytesAt_add bytesAt_writeBytes_sep)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_eor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  Proof.Md5.AArch64.Stream.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m))
    (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  Proof.Md5.AArch64.Stream.WP.cons (s' := s.write .x d (s.gpr n <<< sh))
    (by simp [exec, h, State.read]) (k _ (Upd.write64 _ _ _))

end

/-- The first `n` words of `[dst] ← [x] xor [src]`, for 64-byte blocks `d`,
`x`, `y` in memory, where `d` overlaps neither of the others. The code uses
`x9` and `x10`. -/
theorem xor64_ok {dR xR sR : Reg} (hd : dR ≠ .x9 ∧ dR ≠ .x10) (hx : xR ≠ .x9 ∧ xR ≠ .x10)
    (hs : sR ≠ .x9 ∧ sR ≠ .x10)
    {d x y : Addr} (hdx : Region.Disjoint ⟨d, 64⟩ ⟨x, 64⟩) (hdy : Region.Disjoint ⟨d, 64⟩ ⟨y, 64⟩) :
    ∀ n ≤ 8, ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr dR = d → s.gpr xR = x → s.gpr sR = y →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < 8, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ s', (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp →
      s'.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (xorW dR xR sR) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [bytesAt, xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q gd gx gy hinx hiny hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q gd gx gy hinx hiny hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    refine wp_ldr (a := x + BitVec.ofNat 64 (8 * n)) ⟨by omega, by omega⟩
      (by rw [g₁ _ hx.1 hx.2, gx]) (by rw [rd₁, wr₁]; exact hinx n (by omega)) fun s₂ u₂ => ?_
    refine wp_ldr (a := y + BitVec.ofNat 64 (8 * n)) ⟨by omega, by omega⟩
      (by rw [u₂.other _ hs.1, g₁ _ hs.1 hs.2, gy])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact hiny n (by omega)) fun s₃ u₃ => ?_
    refine wp_eor fun s₄ u₄ => ?_
    refine wp_str (a := d + BitVec.ofNat 64 (8 * n)) ⟨by omega, by omega⟩
      (by rw [u₄.other _ hd.1, u₃.other _ hd.2, u₂.other _ hd.1, g₁ _ hd.1 hd.2, gd])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      fun s₅ u₅ => k s₅ (fun r h9 h10 => by
          rw [u₅.gpr, u₄.other r h9, u₃.other r h10, u₂.other r h9, g₁ r h9 h10])
        (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))).length = 8 * n := by
      rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (8 * n), 8⟩ ⟨d, (xorBytes (bytesAt s.mem x (8 * n))
        (bytesAt s.mem y (8 * n))).length⟩ := by
      rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (8 * n), 8⟩ ⟨d, (xorBytes (bytesAt s.mem x (8 * n))
        (bytesAt s.mem y (8 * n))).length⟩ := by
      rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₃.mem, u₂.mem, writeW_xor,
      m₁, bytesAt_writeBytes_sep _ _ sx (by omega), bytesAt_writeBytes_sep _ _ sy (by omega)]
    have e := writeBytes_append s.mem d _ (xorBytes (bytesAt s.mem (x + BitVec.ofNat 64 (8 * n)) 8)
      (bytesAt s.mem (y + BitVec.ofNat 64 (8 * n)) 8))
      (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
    rw [hl] at e
    rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
      List.zipWith_append (by simp [bytesAt])]

end VG.Proof.Scrypt.AArch64.BlockMix
