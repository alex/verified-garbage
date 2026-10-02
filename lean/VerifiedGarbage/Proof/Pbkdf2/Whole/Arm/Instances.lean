import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.CT
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Instances
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: the instances

Untrusted: everything here is checked by Lean. The generic proof
(`CT.lean`) at each hash function of `Proof/Hmac/Generic/Arm/Hashes.lean`:
the functions it calls are verified by their own registration files (with
16 bytes of stack, the most their frames use: `armStack`), the taint checks
are evaluated by the kernel, and a state satisfies the shared contract
(`pbkSat`).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Arm.FrameStack
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Proof.Hmac.Generic.Arm (sha1H md5H sha384H sha512H' sha512_224H sha512_256H sha1OK md5OK sha384OK
  sha512OK sha512_224OK sha512_256OK)

/-- The functions `pbkdf2` calls for the hash function `M` of the instance
`I` (`Impl/Pbkdf2/Md/Arm.lean`), with the working space of `I`'s functions,
by the names they are registered with. -/
def fnsOf (I : Spec.Hmac.Instance) (M : Impl.Pbkdf2.Md.Arm.Hash) : Fns where
  H := M.st
  W := I.scratch
  hiN := I.initApi.name
  hiC := M.st.init
  hfN := I.finalizeApi.name
  hfC := M.hmacFin
  itN := I.iterateApi.name
  itC := M.iterate

/-- Memory holding the stack arguments `1, 0x1200, 0, 0x2000` of `pbkdf2` at `0x8000`. -/
def pbkMem : Mem := fun a =>
  if a = 0x8000 then 0x01 else if a = 0x8005 then 0x12 else if a = 0x800D then 0x20 else 0

/-- A state satisfying `pbkdf2`'s precondition with `8 W` bytes of scratch
space: an empty password, salt and output, and one iteration. -/
def pbkSat (W : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x1100
    | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := pbkMem
  rd := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩, ⟨0x8000, 16⟩]
  wr := [⟨0x1200, 0⟩, ⟨0x2000, W * 8⟩]

/-! ## SHA-1 -/

def sha1F : Fns := fnsOf Spec.Hmac.sha1I Md.Arm.sha1Md

theorem sha1_checks : Checks sha1F := by
  constructor <;> exact ⟨_, by taint_decide⟩

def sha1OKF : FnsOK sha1F where
  hH := sha1OK
  Wi := 56
  Wf := 56
  Wt := 56
  hi := .of_verified Proof.Hmac.Generic.Arm.Instances.sha1_init
  hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha1_finalize
  it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha1_iterate
  hiSt := by decide +kernel
  hfSt := by decide +kernel
  itSt := by decide +kernel
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide
  reach := by decide
  encB1 := by decide
  encB := by decide
  encB4 := by decide
  encD := by decide

theorem sha1_sat : ∃ s, (Spec.Hmac.sha1I.pbkdf2Contract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using pbkSat 140

theorem sha1 : Verified Arm.target sha1F.pbkdf2 (Spec.Hmac.sha1I.pbkdf2Contract Arm.abi 24) :=
  verified sha1OKF sha1_checks rfl rfl sha1_sat

/-! ## MD5 -/

def md5F : Fns := fnsOf Spec.Hmac.md5I Md.Arm.md5Md

theorem md5_checks : Checks md5F := by
  constructor <;> exact ⟨_, by taint_decide⟩

def md5OKF : FnsOK md5F where
  hH := md5OK
  Wi := 48
  Wf := 48
  Wt := 48
  hi := .of_verified Proof.Hmac.Generic.Arm.Instances.md5_init
  hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.md5_finalize
  it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.md5_iterate
  hiSt := by decide +kernel
  hfSt := by decide +kernel
  itSt := by decide +kernel
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide
  reach := by decide
  encB1 := by decide
  encB := by decide
  encB4 := by decide
  encD := by decide

theorem md5_sat : ∃ s, (Spec.Hmac.md5I.pbkdf2Contract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using pbkSat 128

theorem md5 : Verified Arm.target md5F.pbkdf2 (Spec.Hmac.md5I.pbkdf2Contract Arm.abi 24) :=
  verified md5OKF md5_checks rfl rfl md5_sat

/-! ## SHA-384 -/

def sha384F : Fns := fnsOf Spec.Hmac.sha384I Md.Arm.sha384Md

theorem sha384_checks : Checks sha384F := by
  constructor <;> exact ⟨_, by taint_decide⟩

def sha384OKF : FnsOK sha384F where
  hH := sha384OK
  Wi := 234
  Wf := 234
  Wt := 234
  hi := .of_verified Proof.Hmac.Generic.Arm.Instances.sha384_init
  hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha384_finalize
  it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha384_iterate
  hiSt := by decide +kernel
  hfSt := by decide +kernel
  itSt := by decide +kernel
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide
  reach := by decide
  encB1 := by decide
  encB := by decide
  encB4 := by decide
  encD := by decide

theorem sha384_sat : ∃ s, (Spec.Hmac.sha384I.pbkdf2Contract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using pbkSat 426

theorem sha384 : Verified Arm.target sha384F.pbkdf2 (Spec.Hmac.sha384I.pbkdf2Contract Arm.abi 24) :=
  verified sha384OKF sha384_checks rfl rfl sha384_sat

/-! ## SHA-512 -/

def sha512F : Fns := fnsOf Spec.Hmac.sha512I Md.Arm.sha512Md'

theorem sha512_checks : Checks sha512F := by
  constructor <;> exact ⟨_, by taint_decide⟩

def sha512OKF : FnsOK sha512F where
  hH := sha512OK
  Wi := 234
  Wf := 234
  Wt := 234
  hi := .of_verified Proof.Hmac.Generic.Arm.Instances.sha512_init
  hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_finalize
  it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_iterate
  hiSt := by decide +kernel
  hfSt := by decide +kernel
  itSt := by decide +kernel
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide
  reach := by decide
  encB1 := by decide
  encB := by decide
  encB4 := by decide
  encD := by decide

theorem sha512_sat : ∃ s, (Spec.Hmac.sha512I.pbkdf2Contract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using pbkSat 426

theorem sha512 : Verified Arm.target sha512F.pbkdf2 (Spec.Hmac.sha512I.pbkdf2Contract Arm.abi 24) :=
  verified sha512OKF sha512_checks rfl rfl sha512_sat

/-! ## SHA-512/224 -/

def sha512_224F : Fns := fnsOf Spec.Hmac.sha512_224I Md.Arm.sha512_224Md

theorem sha512_224_checks : Checks sha512_224F := by
  constructor <;> exact ⟨_, by taint_decide⟩

def sha512_224OKF : FnsOK sha512_224F where
  hH := sha512_224OK
  Wi := 234
  Wf := 234
  Wt := 234
  hi := .of_verified Proof.Hmac.Generic.Arm.Instances.sha512_224_init
  hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_224_finalize
  it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_224_iterate
  hiSt := by decide +kernel
  hfSt := by decide +kernel
  itSt := by decide +kernel
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide
  reach := by decide
  encB1 := by decide
  encB := by decide
  encB4 := by decide
  encD := by decide

theorem sha512_224_sat : ∃ s, (Spec.Hmac.sha512_224I.pbkdf2Contract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using pbkSat 426

theorem sha512_224 : Verified Arm.target sha512_224F.pbkdf2 (Spec.Hmac.sha512_224I.pbkdf2Contract Arm.abi 24) :=
  verified sha512_224OKF sha512_224_checks rfl rfl sha512_224_sat

/-! ## SHA-512/256 -/

def sha512_256F : Fns := fnsOf Spec.Hmac.sha512_256I Md.Arm.sha512_256Md

theorem sha512_256_checks : Checks sha512_256F := by
  constructor <;> exact ⟨_, by taint_decide⟩

def sha512_256OKF : FnsOK sha512_256F where
  hH := sha512_256OK
  Wi := 234
  Wf := 234
  Wt := 234
  hi := .of_verified Proof.Hmac.Generic.Arm.Instances.sha512_256_init
  hf := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_256_finalize
  it := .of_verified Proof.Pbkdf2.Md.Arm.Instances.sha512_256_iterate
  hiSt := by decide +kernel
  hfSt := by decide +kernel
  itSt := by decide +kernel
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide
  reach := by decide
  encB1 := by decide
  encB := by decide
  encB4 := by decide
  encD := by decide

theorem sha512_256_sat : ∃ s, (Spec.Hmac.sha512_256I.pbkdf2Contract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using pbkSat 426

theorem sha512_256 : Verified Arm.target sha512_256F.pbkdf2 (Spec.Hmac.sha512_256I.pbkdf2Contract Arm.abi 24) :=
  verified sha512_256OKF sha512_256_checks rfl rfl sha512_256_sat

end VG.Proof.Pbkdf2.Whole.Arm
