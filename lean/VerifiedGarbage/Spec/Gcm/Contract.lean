import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.Artifact

/-!
# AES-GCM: the contracts of counter mode and GHASH, on every target

**Trusted** (as every file in `Spec/`). The contracts of the two primitives
AES-GCM is built from, in terms of `Spec/Gcm.lean`, for any target: `A` is
the target's calling convention. The signatures fix where the arguments are,
the memory each function may access, disjointness, and that the pointers,
the lengths and the number of rounds are public (see `TCB/Sig.lean`).

* `vg_aes_ctr32` XORs AES counter-mode keystream (with GCM's `inc₃₂`) into
  whole blocks in place, from a key schedule that `vg_aes_expand_key`
  (`VG.Spec.Aes.expandKeyContract`) wrote. With a zero block it computes
  `H = CIPH_K(0¹²⁸)`, and with `S` it computes the unmasked tag
  `S ⊕ CIPH_K(J₀)`.
* `vg_ghash` continues `GHASH_H` over whole blocks.

The rest of GCM-AE and GCM-AD (`J₀`, the final partial block, padding, the
length block, truncating and comparing the tag, and the length limits) is
the caller's job.

Each takes a `scratch` buffer of working space, sized for the target that
needs the most, and the number of bytes of stack below the stack pointer
that an implementation's calls use (`stack`, see `Sig.contract`), 0 for
one that makes no call.
-/

namespace VG.Spec.Gcm

/-- `vg_aes_ctr32(schedule: *const [u8; 240], rounds: usize, counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])`.
`rounds` is public; `scratch` is working space. -/
def ctr32Sig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("counter", .array true .u8 16), ("data", .slice true (.array .u8 16) "n"),
    ("scratch", .array true .u64 256)]

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: XORs `CIPH_K(CB₁) … CIPH_K(CBₙ)`
into the `n` blocks at `data`, where `CB₁` is the block at `counter` and
`CBᵢ₊₁ = inc₃₂(CBᵢ)`, and leaves `inc₃₂ⁿ(CB₁)` at `counter`. The key
schedule, the counter and the data are secret. -/
def ctr32Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ctr32Sig.contract A
    (pre := fun _schedule rounds _counter _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds counter data n _scratch m m' _ =>
      let ciph := aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      blocksAt m' data n.toNat = ctr32 ciph (blockAt m counter) (blocksAt m data n.toNat) ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter))
    (stack := stack)

/-- `vg_ghash(h: *const [u8; 16], y: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 32])`.
`scratch` is working space. -/
def ghashSig : Sig where
  params := [("h", .array false .u8 16), ("y", .array true .u8 16),
    ("data", .slice false (.array .u8 16) "n"), ("scratch", .array true .u64 32)]

/-- With the hash subkey `H` at `h` and a block `Y` at `y`: replaces `Y`
with `GHASH_H` continued from `Y` over the `n` blocks at `data`
(`Yᵢ = (Yᵢ₋₁ ⊕ Xᵢ) • H`). The hash subkey, `Y` and the data are secret. -/
def ghashContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ghashSig.contract A (post := fun h y data n _scratch m m' _ =>
    blockAt m' y = ghashFrom (blockAt m h) (blockAt m y) (blocksAt m data n.toNat))
    (stack := stack)

end VG.Spec.Gcm
