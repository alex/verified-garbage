import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hashes
import VerifiedGarbage.Proof.Sha256.X86.Shared
import VerifiedGarbage.Proof.Sha256.X86.Variants.Code

/-!
# SHA-256's streaming functions on x86 (32-bit), for every backend

SHA-256 has an implementation of its compression function for each variant
of its interface on x86 (`Variants/Sha256/X86/`), and its streaming `update`
and `finalize` made with each (`Sha256Stream`, verified for any initial hash
value): `sha256OK` is `HashOK` for any of them, with `vg_sha256_init`.
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Sha256.X86.Variants (hmacHash)

/-- SHA-256's streaming `update` and `finalize` made with one implementation
of its compression function, named with its suffix (e.g. `_shani`; nothing
for the baseline implementation), verified against their per-target
contracts, which hold from any initial hash value; they keep `esp` and use
at most 20 bytes of stack. -/
structure Sha256Stream where
  suffix : String
  upd : Prog isa
  fin : Prog isa
  updOK : Verified X86.target upd Proof.Sha256.updateX86
  finOK : Verified X86.target fin Proof.Sha256.finalizeX86
  updSp : NoSp upd
  finSp : NoSp fin
  updSU : stackUse upd ≤ 20
  finSU : stackUse fin ≤ 20

/-- SHA-256's streaming functions with `v`'s `update` and `finalize`. -/
abbrev sha256H (v : Sha256Stream) : Hash := hmacHash v.suffix v.upd v.fin

theorem sha256_initSp : NoSp Impl.Sha256.X86.Stream.init := nosp_of (by lit_decide)
theorem sha256_initSU : stackUse Impl.Sha256.X86.Stream.init ≤ 20 := by lit_decide

/-- SHA-256's streaming functions with `v`'s `update` and `finalize`, verified. -/
def sha256OK (v : Sha256Stream) : HashOK (sha256H v) where
  SH := Spec.Hmac.sha256S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := show 32 ≤ 32 by decide
  hF := show 32 ≤ 64 by decide
  hD0 := show 0 < 32 by decide
  hS0 := show 0 < 96 by decide
  hSB := show 96 ≤ 256 by decide
  hB0 := show 0 < 64 by decide
  hBB := show 64 ≤ 128 by decide
  hWb := show 160 ≤ 8 * 20 by decide
  hW := show 20 ≤ 64 by decide
  repr := Hmac.Generic.Common.sha256_repr
  init := Proof.Sha256.X86.Stream.init_verified
  upd := v.updOK.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.updOK.2.2 }
  fin := v.finOK.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 32 (Spec.Sha256.bytesAt s'.mem _ 32) = _
        rw [List.take_of_length_le (by simp [Spec.Sha256.bytesAt])]
        exact h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.finOK.2.2 }
  initSp := sha256_initSp
  updSp := v.updSp
  finSp := v.finSp
  initSU := sha256_initSU
  updSU := v.updSU
  finSU := v.finSU

end VG.Proof.Pbkdf2.Stream.X86
