import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Hmac.Generic.X86.Lit
import VerifiedGarbage.Proof.Hmac.Generic.X86.InitCT
import VerifiedGarbage.Proof.Hmac.Generic.X86.Hashes

/-!
# HMAC over the streaming hash functions on x86 (32-bit): the instances of `init`

Untrusted: everything here is checked by Lean. The generic proof of `init`
(`InitCT.lean`) at each hash function of `Hashes.lean`, moved to the shared
contract of `Spec/Hmac/Generic.lean` (`sig_implies`), which the artifacts
are emitted with. `finalize` is written over the compression function
instead: `Proof/Pbkdf2/Md/X86/Instances.lean`.
-/

namespace VG.Proof.Hmac.Generic.X86.Instances

open VG.X86
open VG.Proof.Hmac.Generic.X86

/-- Memory holding the arguments `0x1000, 0x1400, 0x1800, 0, 0x2000` of
`init` at `0x6004`. -/
def initMem : Mem := fun a =>
  if a = 0x6005 then 0x10 else if a = 0x6009 then 0x14 else if a = 0x600D then 0x18 else
  if a = 0x6015 then 0x20 else 0

/-- A state satisfying `init`'s precondition, with states of `S` bytes and
`8 sc` bytes of scratch space (and an empty key), with the arguments writable. -/
def initSat (S sc : Nat) : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := initMem
  rd := [⟨0x1800, 0⟩]
  wr := [⟨0x1000, S⟩, ⟨0x1400, S⟩, ⟨0x2000, 8 * sc⟩, ⟨0x6004, 20⟩]

theorem initSat_args (S sc : Nat) :
    arg (initSat S sc) 0 = 0x1000 ∧ arg (initSat S sc) 1 = 0x1400 ∧ arg (initSat S sc) 2 = 0x1800 ∧
      arg (initSat S sc) 3 = 0 ∧ arg (initSat S sc) 4 = 0x2000 ∧ argAddr (initSat S sc) 0 = 0x6004 ∧
      (initSat S sc).gpr .esp = 0x6000 := by
  have e : ∀ i, arg (initSat S sc) i = arg (initSat 0 0) i := fun _ => rfl
  have e' : argAddr (initSat S sc) 0 = argAddr (initSat 0 0) 0 := rfl
  rw [e, e, e, e, e, e']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> decide

/-! ## SHA-1 -/

theorem sha1_initChecks : Init.Checks sha1H where
  keys := ⟨_, by taint_decide⟩
  states := ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha1_initImp : (initW Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.initContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 84 56
  sig_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 84 56

theorem sha1_init : Verified X86.target sha1H.init (Spec.Hmac.sha1I.initContract X86.abi 48) :=
  (Init.verifiedW sha1OK sha1_initChecks (by decide) sha1_initImp.sat_left).of_implies sha1_initImp

/-! ## MD5 -/

theorem md5_initChecks : Init.Checks md5H where
  keys := ⟨_, by taint_decide⟩
  states := ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem md5_initImp : (initW Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.initContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 80 48
  sig_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 80 48

theorem md5_init : Verified X86.target md5H.init (Spec.Hmac.md5I.initContract X86.abi 48) :=
  (Init.verifiedW md5OK md5_initChecks (by decide) md5_initImp.sat_left).of_implies md5_initImp

/-- `Init.Checks` looks at the sizes of a hash function but its digest's. -/
theorem Init.Checks.of_eq {H H' : Impl.Hmac.Generic.X86.Hash} (hB : H.B = H'.B) (hS : H.S = H'.S)
    (hW : H.W = H'.W) (h : Init.Checks H) : Init.Checks H' := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hB hS hW; subst hB hS hW
  exact ⟨h.keys, h.states, h.upd, h.restore⟩

/-! ## SHA-384 -/

theorem sha384_initChecks : Init.Checks sha384H where
  keys := ⟨_, by taint_decide⟩
  states := ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha384_initImp : (initW Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.initContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 192 234
  sig_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 192 234

theorem sha384_init : Verified X86.target sha384H.init (Spec.Hmac.sha384I.initContract X86.abi 48) :=
  (Init.verifiedW sha384OK sha384_initChecks (by decide) sha384_initImp.sat_left).of_implies sha384_initImp

/-! ## SHA-512 -/

theorem sha512_initChecks : Init.Checks sha512H' :=
  Init.Checks.of_eq (H := sha384H) rfl rfl rfl sha384_initChecks

theorem sha512_initImp : (initW Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.initContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 192 234
  sig_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 192 234

theorem sha512_init : Verified X86.target sha512H'.init (Spec.Hmac.sha512I.initContract X86.abi 48) :=
  (Init.verifiedW sha512OK sha512_initChecks (by decide) sha512_initImp.sat_left).of_implies sha512_initImp

/-! ## SHA-512/224 -/

theorem sha512_224_initChecks : Init.Checks sha512_224H :=
  Init.Checks.of_eq (H := sha384H) rfl rfl rfl sha384_initChecks

theorem sha512_224_initImp : (initW Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.initContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 192 234
  sig_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 192 234

theorem sha512_224_init : Verified X86.target sha512_224H.init (Spec.Hmac.sha512_224I.initContract X86.abi 48) :=
  (Init.verifiedW sha512_224OK sha512_224_initChecks (by decide) sha512_224_initImp.sat_left).of_implies sha512_224_initImp

/-! ## SHA-512/256 -/

theorem sha512_256_initChecks : Init.Checks sha512_256H :=
  Init.Checks.of_eq (H := sha384H) rfl rfl rfl sha384_initChecks

theorem sha512_256_initImp : (initW Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.initContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 192 234
  sig_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 192 234

theorem sha512_256_init : Verified X86.target sha512_256H.init (Spec.Hmac.sha512_256I.initContract X86.abi 48) :=
  (Init.verifiedW sha512_256OK sha512_256_initChecks (by decide) sha512_256_initImp.sat_left).of_implies sha512_256_initImp

end VG.Proof.Hmac.Generic.X86.Instances
