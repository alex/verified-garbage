import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.CT
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface

/-!
# PBKDF2-HMAC-SHA-256 on x86 (32-bit), the whole derivation, for every backend

The generic proof (`CT.lean`) at SHA-256, for any backend
(`Proof/Sha256/X86/Variants/Interface.lean`): its streaming functions,
HMAC's `init` and `finalize` and PBKDF2's iteration made with the backend,
verified for any backend against the shared contracts
(`Proof.Sha256.X86.Variants.Backend.hmacInit` and the others), as for the
other hash functions (`Instances.lean`). The taint checks depend only on the
sizes, so they are evaluated once, for any backend (`sha256Shape`).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Sha256.X86.Variants (Backend)

/-- The functions `pbkdf2` calls for SHA-256 with the backend `v`, verified. -/
def sha256OKF (v : Backend) : FnsOK v.F where
  hH := Proof.Hmac.Generic.X86.sha256OK v.stream
  Wi := 104
  Wf := 104
  Wt := 104
  hi := .of_verified v.hmacInit
  hf := .of_verified v.hmacFin
  it := .of_verified v.iterate
  hiSp := v.initNoSp
  hfSp := v.finalizeNoSp
  itSp := v.iterNoSp
  hiSU := v.initStack
  hfSU := v.finalizeStack
  itSU := v.iterStack
  hWi := show 104 ≤ 104 by decide
  hWf := show 104 ≤ 104 by decide
  hWt := show 104 ≤ 104 by decide
  hWH := show 20 ≤ 104 by decide
  hW := show 104 ≤ 512 by decide
  hDB := show 32 ≤ 64 by decide
  hBS := show 64 ≤ 96 by decide
  fits := show 20 + 2 * 32 + 32 ≤ 4 * 96 by decide

/-- The sizes of `Backend.F`, which are all the taint checks depend on. -/
def sha256Shape : Fns := Proof.Sha256.X86.Variants.fns "" "" (.block []) (.block []) (.block [])

theorem sha256Shape_checks : Checks sha256Shape where
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

theorem sha256_checks (v : Backend) : Checks v.F :=
  let h := sha256Shape_checks
  ⟨h.pro, h.cmp, h.hk1, h.hk3, h.hk5, h.hk7, h.short, h.su1, h.su3, h.su4, h.init, h.b1, h.b2, h.b4, h.b6, h.b7,
    h.tail, h.restore⟩

theorem sha256_sat : ∃ s, (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using pbkSat 200

/-- `pbkdf2` for SHA-256 with the backend `v`, verified. -/
theorem sha256_verified (v : Backend) :
    Verified X86.target v.F.pbkdf2 (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76) :=
  verified (sha256OKF v) (sha256_checks v) rfl rfl sha256_sat

end VG.Proof.Pbkdf2.Whole.X86
