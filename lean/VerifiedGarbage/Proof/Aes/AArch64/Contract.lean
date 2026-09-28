import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.AArch64.Target

/-!
# AES: the AArch64 contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`). The contracts of the AArch64 implementations of AES
counter mode and the key expansion, in terms of `Spec/Gcm.lean` and
`Spec/Aes.lean`.
-/

namespace VG.Proof.Aes

open Spec.Gcm

open AArch64 in
/-- AArch64 contract for
`vg_aes_ctr32(schedule: *const [u8; 240], rounds: usize, counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])`:
XORs the AES counter-mode keystream from the counter block at `counter`
into the `n` blocks at `data`, and advances the counter block by `n`.

The code may read `schedule` (240 bytes) and read and write `counter` (16
bytes), `data` (`16 n` bytes) and `scratch` (2048 bytes, whose contents on
exit are unspecified). These may not overlap each other, and `data` may not
wrap around the end of the address space. `rounds` is 10, 12 or 14. The
pointers, `rounds` and `n` are public; the key schedule, the counter block
and the data are secret. -/
def ctr32AArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let counter : Region := ⟨s.gpr .x2, 16⟩
    let data : Region := ⟨s.gpr .x3, 16 * (s.gpr .x4).toNat⟩
    let scratch : Region := ⟨s.gpr .x5, 2048⟩
    s.rd = [sched] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x3).toNat + 16 * (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    let ciph := aesWith (s.gpr .x1).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))
    blocksAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat =
        ctr32 ciph (blockAt s.mem (s.gpr .x2)) (blocksAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) ∧
      blockAt s'.mem (s.gpr .x2) = Nat.repeat inc32 (s.gpr .x4).toNat (blockAt s.mem (s.gpr .x2))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp

open AArch64 in
/-- AArch64 contract for
`vg_aes_expand_key(key: *const u8, key_len: usize, schedule: *mut [u8; 240], scratch: *mut [u64; 64])`:
writes the key schedule of the `key_len`-byte key at `key` to `schedule`.

The code may read `key` (`key_len` bytes) and read and write `schedule`
(240 bytes) and `scratch` (512 bytes, whose contents on exit are
unspecified). These may not overlap each other. `key_len` is 16, 24 or 32.
The pointers and `key_len` are public; the key is secret. -/
def expandKeyAArch64 : Contract AArch64.isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let sched : Region := ⟨s.gpr .x2, 240⟩
    let scratch : Region := ⟨s.gpr .x3, 512⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    ((s.gpr .x1).toNat = 16 ∨ (s.gpr .x1).toNat = 24 ∨ (s.gpr .x1).toNat = 32)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) (16 * (Spec.Aes.rounds ((s.gpr .x1).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes
