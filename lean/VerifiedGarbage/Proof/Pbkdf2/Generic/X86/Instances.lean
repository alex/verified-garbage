import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Hmac.Generic.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Generic.X86.IterateCT
import VerifiedGarbage.Proof.Hmac.Generic.X86.Hashes

/-!
# PBKDF2-HMAC over the streaming hash functions on x86 (32-bit): the instances

As for HMAC (`Proof/Hmac/Generic/X86/Instances.lean`): the generic proof
(`IterateCT.lean`) at each hash function of
`Proof/Hmac/Generic/X86/Hashes.lean`, moved to the shared contract of
`Spec/Pbkdf2/Generic.lean` (`sig_implies`), which the artifacts are emitted
with.
-/

namespace VG.Proof.Pbkdf2.Generic.X86.Instances

open VG.X86
open VG.Proof.Hmac.Generic.X86
open VG.Proof.Pbkdf2.Generic.X86

/-- Memory holding the arguments `0x1000, 0x1400, 0, 0x1800, 0x2000` of
`iterate` at `0x6004`. -/
def iterMem : Mem := fun a =>
  if a = 0x6005 then 0x10 else if a = 0x6009 then 0x14 else if a = 0x6011 then 0x18 else
  if a = 0x6015 then 0x20 else 0

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `8 sc` bytes of scratch space, with the arguments
writable. -/
def iterSat (S D sc : Nat) : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := iterMem
  rd := [⟨0x1000, 2 * S⟩, ⟨0x1400, D⟩]
  wr := [⟨0x1800, D⟩, ⟨0x2000, 8 * sc⟩, ⟨0x6004, 20⟩]

theorem iterSat_args (S D sc : Nat) :
    arg (iterSat S D sc) 0 = 0x1000 ∧ arg (iterSat S D sc) 1 = 0x1400 ∧ arg (iterSat S D sc) 2 = 0 ∧
      arg (iterSat S D sc) 3 = 0x1800 ∧ arg (iterSat S D sc) 4 = 0x2000 ∧ argAddr (iterSat S D sc) 0 = 0x6004 ∧
      (iterSat S D sc).gpr .esp = 0x6000 := by
  have e : ∀ i, arg (iterSat S D sc) i = arg (iterSat 0 0 0) i := fun _ => rfl
  have e' : argAddr (iterSat S D sc) 0 = argAddr (iterSat 0 0 0) 0 := rfl
  rw [e, e, e, e, e, e']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> decide

/-! ## SHA-1 -/

theorem sha1_checks : Checks sha1H where
  pro := ⟨_, by taint_decide⟩
  copyU := ⟨_, by taint_decide⟩
  copyK := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  fin := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  xor := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha1_imp : (iterW Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 84 20 56
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 84 20 56

theorem sha1 : Verified X86.target (Impl.Pbkdf2.Generic.X86.iterate sha1H)
    (Spec.Hmac.sha1I.iterateContract X86.abi 48) :=
  (verifiedW sha1OK sha1_checks (by decide) sha1_imp.sat_left).of_implies sha1_imp

/-! ## MD5 -/

theorem md5_checks : Checks md5H where
  pro := ⟨_, by taint_decide⟩
  copyU := ⟨_, by taint_decide⟩
  copyK := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  fin := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  xor := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem md5_imp : (iterW Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 80 16 48
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 80 16 48

theorem md5 : Verified X86.target (Impl.Pbkdf2.Generic.X86.iterate md5H)
    (Spec.Hmac.md5I.iterateContract X86.abi 48) :=
  (verifiedW md5OK md5_checks (by decide) md5_imp.sat_left).of_implies md5_imp

/-! ## SHA-384 -/

theorem sha384_checks : Checks sha384H where
  pro := ⟨_, by taint_decide⟩
  copyU := ⟨_, by taint_decide⟩
  copyK := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  fin := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  xor := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha384_imp : (iterW Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 192 48 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 192 48 234

theorem sha384 : Verified X86.target (Impl.Pbkdf2.Generic.X86.iterate sha384H)
    (Spec.Hmac.sha384I.iterateContract X86.abi 48) :=
  (verifiedW sha384OK sha384_checks (by decide) sha384_imp.sat_left).of_implies sha384_imp

/-! ## SHA-512 -/

theorem sha512_checks : Checks sha512H' where
  pro := ⟨_, by taint_decide⟩
  copyU := ⟨_, by taint_decide⟩
  copyK := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  fin := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  xor := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_imp : (iterW Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 192 64 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 192 64 234

theorem sha512 : Verified X86.target (Impl.Pbkdf2.Generic.X86.iterate sha512H')
    (Spec.Hmac.sha512I.iterateContract X86.abi 48) :=
  (verifiedW sha512OK sha512_checks (by decide) sha512_imp.sat_left).of_implies sha512_imp

/-! ## SHA-512/224 -/

theorem sha512_224_checks : Checks sha512_224H where
  pro := ⟨_, by taint_decide⟩
  copyU := ⟨_, by taint_decide⟩
  copyK := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  fin := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  xor := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_224_imp : (iterW Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 192 28 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 192 28 234

theorem sha512_224 : Verified X86.target (Impl.Pbkdf2.Generic.X86.iterate sha512_224H)
    (Spec.Hmac.sha512_224I.iterateContract X86.abi 48) :=
  (verifiedW sha512_224OK sha512_224_checks (by decide) sha512_224_imp.sat_left).of_implies sha512_224_imp

/-! ## SHA-512/256 -/

theorem sha512_256_checks : Checks sha512_256H where
  pro := ⟨_, by taint_decide⟩
  copyU := ⟨_, by taint_decide⟩
  copyK := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  fin := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  xor := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_256_imp : (iterW Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 192 32 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 192 32 234

theorem sha512_256 : Verified X86.target (Impl.Pbkdf2.Generic.X86.iterate sha512_256H)
    (Spec.Hmac.sha512_256I.iterateContract X86.abi 48) :=
  (verifiedW sha512_256OK sha512_256_checks (by decide) sha512_256_imp.sat_left).of_implies sha512_256_imp

end VG.Proof.Pbkdf2.Generic.X86.Instances
