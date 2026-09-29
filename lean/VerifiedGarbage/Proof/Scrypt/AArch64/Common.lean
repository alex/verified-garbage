import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Impl.Scrypt.AArch64.BlockMix
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# scrypt on AArch64: common lemmas

Untrusted: everything here is checked by Lean. The target-independent lemmas
about addresses and bytes are in `Proof/Scrypt/Memory.lean`; here are the
weakest-precondition rules for the AArch64 forms, and the 64-byte
exclusive-or.
-/

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for `vg_scrypt_blockmix(b = x0, r = x1, y = x2, ry = x3, scratch = x4)`:
if `ry = r > 0`, writes scryptBlockMix of the `128 r` bytes at `b` to `y`.
Its frame (saving `x30`) is the 16 bytes below the stack pointer. -/
def blockMixAArch64 : Contract AArch64.isa where
  pre s :=
    let r := (s.gpr .x1).toNat
    let b : Region := ⟨s.gpr .x0, r * 128⟩
    let y : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .x4, 128⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [b] ∧ s.wr = [y, scratch] ∧
    y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint b ∧ stack.Disjoint y ∧ stack.Disjoint scratch ∧
    (s.gpr .x0).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + 128 ≤ 2 ^ 64 ∧
    s.gpr .x3 = s.gpr .x1 ∧ 0 < r
  post s s' := let r := (s.gpr .x1).toNat
    bytesAt s'.mem (s.gpr .x2) (128 * r) = blockMix r (bytesAt s.mem (s.gpr .x0) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for
`vg_scrypt_romix(b = x0, r = x1, v = x2, vlen = x3, scratch = x4, slen = x5)`:
if `r > 0`, `vlen = N r` for a power of two `N`, and `slen = r + 2`, replaces
the `128 r` bytes at `b` by their scryptROMix. It has no frame (it saves `x30`
in `scratch`); its calls of `vg_scrypt_blockmix` use the 16 bytes below the
stack pointer. The indices `j` of step 3 are public. -/
def roMixAArch64 : Contract AArch64.isa where
  pre s :=
    let r := (s.gpr .x1).toNat
    let b : Region := ⟨s.gpr .x0, r * 128⟩
    let v : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat * 128⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [b, v, scratch] ∧
    b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint b ∧ stack.Disjoint v ∧ stack.Disjoint scratch ∧
    (s.gpr .x0).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat * 128 ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .x3).toNat % r = 0 ∧ ((s.gpr .x3).toNat / r).isPowerOfTwo ∧
    (s.gpr .x5).toNat = r + 2
  post s s' := let r := (s.gpr .x1).toNat
    bytesAt s'.mem (s.gpr .x0) (128 * r) =
      roMix r ((s.gpr .x3).toNat / r) (bytesAt s.mem (s.gpr .x0) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp ∧
    roMixIndices (s₁.gpr .x1).toNat ((s₁.gpr .x3).toNat / (s₁.gpr .x1).toNat)
        (bytesAt s₁.mem (s₁.gpr .x0) (128 * (s₁.gpr .x1).toNat)) =
      roMixIndices (s₂.gpr .x1).toNat ((s₂.gpr .x3).toNat / (s₂.gpr .x1).toNat)
        (bytesAt s₂.mem (s₂.gpr .x0) (128 * (s₂.gpr .x1).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_ldr wp_str)
open VG.Proof.Scrypt.Memory (sub_off writeW_xor xorBytes_length bytesAt_length
  bytesAt_add bytesAt_writeBytes_sep)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_eor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m))
    (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n <<< sh))
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
