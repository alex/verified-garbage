import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.TCB.Artifact

/-!
# AES: the contract of the key expansion, on every target

**Trusted** (as every file in `Spec/`). The contract of
`vg_aes_expand_key`, in terms of `Spec/Aes.lean`, for any target: `A` is
the target's calling convention. The signature fixes where the arguments
are, the memory the function may access, disjointness, and that the
pointers and the key's length are public (see `TCB/Sig.lean`).

The key schedule is stored as plain bytes (the words `w[0] … w[4Nr + 3]` in
order, each as its 4 bytes), which is also the layout AES-NI's round keys
use, so that every implementation of AES on a target reads the same
schedule.
-/

namespace VG.Spec.Aes

/-- `vg_aes_expand_key(key: *const u8, key_len: usize, schedule: *mut [u8; 240], scratch: *mut [u64; 64])`.
The first `16 (Nr + 1)` bytes of `schedule` hold the key schedule on exit;
the rest of it, and `scratch`, are working space. -/
def expandKeySig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("schedule", .array true .u8 240),
    ("scratch", .array true .u64 64)]

/-- For a key of 16, 24 or 32 bytes at `key`, writes its key schedule
(`expandKey`, `16 (Nr + 1)` bytes for `Nr = key_len / 4 + 6` rounds) to
`schedule`. The key is secret. -/
def expandKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeySig.contract A
    (pre := fun _key keyLen _schedule _scratch _ =>
      keyLen.toNat = 16 ∨ keyLen.toNat = 24 ∨ keyLen.toNat = 32)
    (post := fun key keyLen schedule _scratch m m' _ =>
      bytesAt m' schedule (16 * (rounds (keyLen.toNat / 4) + 1)) =
        expandKey (bytesAt m key keyLen.toNat))
    (stack := stack)

end VG.Spec.Aes
