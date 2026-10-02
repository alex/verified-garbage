import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.CT
import VerifiedGarbage.Proof.Hmac.Generic.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the instances

The generic proof (`CT.lean`) at each hash function of
`Proof/Pbkdf2/Md/X86/Hashes.lean`: the functions it calls are verified by
their own registration files, the taint checks are evaluated by the kernel,
and a state satisfies the shared contract (`pbkSat`).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Hmac.Generic.X86 (nosp_of sha1OK md5OK sha384OK sha512OK sha512_224OK sha512_256OK)

/-! ## SHA-1 -/

theorem sha1_checks : Checks sha1F where
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

def sha1OKF : FnsOK sha1F where
  hH := sha1OK
  Wi := 56
  Wf := 56
  Wt := 56
  hi := .of_verified Proof.Hmac.Generic.X86.Instances.sha1_init
  hf := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha1_finalize
  it := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha1_iterate
  hiSp := nosp_of (by lit_decide)
  hfSp := nosp_of (by lit_decide)
  itSp := nosp_of (by lit_decide)
  hiSU := by lit_decide
  hfSU := by lit_decide
  itSU := by lit_decide
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hW := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide

theorem sha1_sat : ∃ s, (Spec.Hmac.sha1I.pbkdf2Contract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using pbkSat 140

theorem sha1 : Verified X86.target sha1F.pbkdf2 (Spec.Hmac.sha1I.pbkdf2Contract X86.abi 76) :=
  verified sha1OKF sha1_checks rfl rfl sha1_sat

/-! ## MD5 -/

theorem md5_checks : Checks md5F where
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

def md5OKF : FnsOK md5F where
  hH := md5OK
  Wi := 48
  Wf := 48
  Wt := 48
  hi := .of_verified Proof.Hmac.Generic.X86.Instances.md5_init
  hf := .of_verified Proof.Pbkdf2.Md.X86.Instances.md5_finalize
  it := .of_verified Proof.Pbkdf2.Md.X86.Instances.md5_iterate
  hiSp := nosp_of (by lit_decide)
  hfSp := nosp_of (by lit_decide)
  itSp := nosp_of (by lit_decide)
  hiSU := by lit_decide
  hfSU := by lit_decide
  itSU := by lit_decide
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hW := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide

theorem md5_sat : ∃ s, (Spec.Hmac.md5I.pbkdf2Contract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using pbkSat 128

theorem md5 : Verified X86.target md5F.pbkdf2 (Spec.Hmac.md5I.pbkdf2Contract X86.abi 76) :=
  verified md5OKF md5_checks rfl rfl md5_sat

/-! ## SHA-384 -/

theorem sha384_checks : Checks sha384F where
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

def sha384OKF : FnsOK sha384F where
  hH := sha384OK
  Wi := 234
  Wf := 234
  Wt := 234
  hi := .of_verified Proof.Hmac.Generic.X86.Instances.sha384_init
  hf := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha384_finalize
  it := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha384_iterate
  hiSp := nosp_of (by lit_decide)
  hfSp := nosp_of (by lit_decide)
  itSp := nosp_of (by lit_decide)
  hiSU := by lit_decide
  hfSU := by lit_decide
  itSU := by lit_decide
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hW := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide

theorem sha384_sat : ∃ s, (Spec.Hmac.sha384I.pbkdf2Contract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using pbkSat 426

theorem sha384 : Verified X86.target sha384F.pbkdf2 (Spec.Hmac.sha384I.pbkdf2Contract X86.abi 76) :=
  verified sha384OKF sha384_checks rfl rfl sha384_sat

/-! ## SHA-512 -/

theorem sha512_checks : Checks sha512F where
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

def sha512OKF : FnsOK sha512F where
  hH := sha512OK
  Wi := 234
  Wf := 234
  Wt := 234
  hi := .of_verified Proof.Hmac.Generic.X86.Instances.sha512_init
  hf := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_finalize
  it := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_iterate
  hiSp := nosp_of (by lit_decide)
  hfSp := nosp_of (by lit_decide)
  itSp := nosp_of (by lit_decide)
  hiSU := by lit_decide
  hfSU := by lit_decide
  itSU := by lit_decide
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hW := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide

theorem sha512_sat : ∃ s, (Spec.Hmac.sha512I.pbkdf2Contract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using pbkSat 426

theorem sha512 : Verified X86.target sha512F.pbkdf2 (Spec.Hmac.sha512I.pbkdf2Contract X86.abi 76) :=
  verified sha512OKF sha512_checks rfl rfl sha512_sat

/-! ## SHA-512/224 -/

theorem sha512_224_checks : Checks sha512_224F where
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

def sha512_224OKF : FnsOK sha512_224F where
  hH := sha512_224OK
  Wi := 234
  Wf := 234
  Wt := 234
  hi := .of_verified Proof.Hmac.Generic.X86.Instances.sha512_224_init
  hf := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_224_finalize
  it := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_224_iterate
  hiSp := nosp_of (by lit_decide)
  hfSp := nosp_of (by lit_decide)
  itSp := nosp_of (by lit_decide)
  hiSU := by lit_decide
  hfSU := by lit_decide
  itSU := by lit_decide
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hW := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide

theorem sha512_224_sat : ∃ s, (Spec.Hmac.sha512_224I.pbkdf2Contract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using pbkSat 426

theorem sha512_224 : Verified X86.target sha512_224F.pbkdf2 (Spec.Hmac.sha512_224I.pbkdf2Contract X86.abi 76) :=
  verified sha512_224OKF sha512_224_checks rfl rfl sha512_224_sat

/-! ## SHA-512/256 -/

theorem sha512_256_checks : Checks sha512_256F where
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

def sha512_256OKF : FnsOK sha512_256F where
  hH := sha512_256OK
  Wi := 234
  Wf := 234
  Wt := 234
  hi := .of_verified Proof.Hmac.Generic.X86.Instances.sha512_256_init
  hf := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_256_finalize
  it := .of_verified Proof.Pbkdf2.Md.X86.Instances.sha512_256_iterate
  hiSp := nosp_of (by lit_decide)
  hfSp := nosp_of (by lit_decide)
  itSp := nosp_of (by lit_decide)
  hiSU := by lit_decide
  hfSU := by lit_decide
  itSU := by lit_decide
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hW := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide

theorem sha512_256_sat : ∃ s, (Spec.Hmac.sha512_256I.pbkdf2Contract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using pbkSat 426

theorem sha512_256 : Verified X86.target sha512_256F.pbkdf2 (Spec.Hmac.sha512_256I.pbkdf2Contract X86.abi 76) :=
  verified sha512_256OKF sha512_256_checks rfl rfl sha512_256_sat

end VG.Proof.Pbkdf2.Whole.X86
