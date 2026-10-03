import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.CT
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface

/-!
# PBKDF2-HMAC-SHA-224 on x86 (32-bit), the whole derivation, for every backend

The generic proof (`CT.lean`) at SHA-224, for any of SHA-256's backends
(`Proof/Sha256/X86/Variants/Interface.lean`): SHA-224's streaming functions,
HMAC's `init` and `finalize` and PBKDF2's iteration made with the backend,
verified for any backend against the shared contracts
(`Proof.Sha256.X86.Variants.Backend.hmacInit224` and the others), as for
SHA-256 (`Sha256.lean`). The taint checks depend only on the sizes, so they
are evaluated once, for any backend (`sha224Shape`).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Sha256.X86.Variants (Backend)

/-- The functions `pbkdf2` calls for SHA-224 with the backend `v`, verified. -/
def sha224OKF (v : Backend) : FnsOK v.F224 where
  hH := Proof.Pbkdf2.Stream.X86.sha224OK v.stream
  Wi := 104
  Wf := 104
  Wt := 104
  hi := .of_verified v.hmacInit224
  hf := .of_verified v.hmacFin224
  it := .of_verified v.iterate224
  hiSp := v.init224NoSp
  hfSp := v.finalize224NoSp
  itSp := v.iter224NoSp
  hiSU := v.init224Stack
  hfSU := v.finalize224Stack
  itSU := v.iter224Stack
  hWi := show 104 ≤ 104 by decide
  hWf := show 104 ≤ 104 by decide
  hWt := show 104 ≤ 104 by decide
  hWH := show 20 ≤ 104 by decide
  hW := show 104 ≤ 512 by decide
  hDB := show 28 ≤ 64 by decide
  hBS := show 64 ≤ 96 by decide
  fits := show 20 + 2 * 28 + 32 ≤ 4 * 96 by decide

/-- The sizes of `Backend.F224`, which are all the taint checks depend on. -/
def sha224Shape : Fns := Proof.Sha256.X86.Variants.fns224 "" "" (.block []) (.block []) (.block [])

theorem sha224Shape_checks : Checks sha224Shape where
  pro := ⟨_, by taint_decide⟩
  cmp := ⟨_, by taint_decide⟩
  hk1 := ⟨_, by taint_decide⟩
  hk3 := ⟨_, by taint_decide⟩
  hk5 := ⟨_, by taint_decide⟩
  hk7 := ⟨_, by taint_decide⟩
  short := ⟨_, by taint_decide⟩
  su1 := ⟨_, by taint_decide⟩
  su3 := ⟨_, by taint_decide⟩
  su4 := ⟨_, by taint_decide⟩
  init := ⟨_, by taint_decide⟩
  b1 := ⟨_, by taint_decide⟩
  b2 := ⟨_, by taint_decide⟩
  b4 := ⟨_, by taint_decide⟩
  b6 := ⟨_, by taint_decide⟩
  b7 := ⟨_, by taint_decide⟩
  tail := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha224_checks (v : Backend) : Checks v.F224 :=
  let h := sha224Shape_checks
  ⟨h.pro, h.cmp, h.hk1, h.hk3, h.hk5, h.hk7, h.short, h.su1, h.su3, h.su4, h.init, h.b1, h.b2, h.b4, h.b6, h.b7,
    h.tail, h.restore⟩

theorem sha224_sat : ∃ s, (Spec.Hmac.sha224I.pbkdf2Contract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using pbkSat 200

/-- `pbkdf2` for SHA-224 with the backend `v`, verified. -/
theorem sha224_verified (v : Backend) :
    Verified X86.target v.F224.pbkdf2 (Spec.Hmac.sha224I.pbkdf2Contract X86.abi 76) :=
  verified (sha224OKF v) (sha224_checks v) rfl rfl sha224_sat

end VG.Proof.Pbkdf2.Whole.X86
