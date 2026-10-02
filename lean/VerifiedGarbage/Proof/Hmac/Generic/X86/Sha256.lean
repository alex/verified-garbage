import VerifiedGarbage.Proof.Hmac.Generic.X86.Instances
import VerifiedGarbage.Proof.Sha256.X86.Shared
import VerifiedGarbage.Proof.Sha256.X86.Variants.Code

/-!
# HMAC-SHA-256 on x86 (32-bit): `init`, for every backend

SHA-256 has an implementation of its compression function for each variant
of its interface on x86 (`Variants/Sha256/X86/`), and its streaming `update`
and `finalize` made with each (`Sha256Stream`, verified for any initial hash
value): `sha256OK` is `HashOK` for any of them, with `vg_sha256_init`. The
generic proof of `init` (`InitCT.lean`) at it is moved to the shared contract
of `Spec.Hmac.sha256I`. Its taint checks depend only on the sizes, so they are
evaluated once, for every backend (`sha256Core`).
-/

namespace VG.Proof.Hmac.Generic.X86

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash)
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
  repr := Common.sha256_repr
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

/-- SHA-256's sizes, without the functions: the code HMAC's `init` runs
between its calls depends on nothing else. -/
def sha256Core : Hash := hmacHash "" (.block []) (.block [])

end VG.Proof.Hmac.Generic.X86

namespace VG.Proof.Hmac.Generic.X86.Instances

open VG.X86
open VG.Proof.Hmac.Generic.X86

theorem sha256_initChecks : Init.Checks sha256Core where
  keys := ⟨_, by taint_decide⟩
  states := ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha256_initImp : (initW Spec.Hmac.sha256S 104).Implies (Spec.Hmac.sha256I.initContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 96 104
  sig_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 96 104

/-- HMAC's `init` with any backend's streaming functions. -/
theorem sha256_init (v : Sha256Stream) :
    Verified X86.target (sha256H v).init (Spec.Hmac.sha256I.initContract X86.abi 48) :=
  (Init.verifiedW (sha256OK v) (Init.Checks.of_eq (H := sha256Core) rfl rfl rfl sha256_initChecks)
    (show 8 * 20 + 16 + 2 * 64 ≤ 8 * 104 by decide) sha256_initImp.sat_left).of_implies sha256_initImp

end VG.Proof.Hmac.Generic.X86.Instances
