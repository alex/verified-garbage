import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.IterateCT
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFinCT

/-!
# HMAC's `finalize` and PBKDF2's `iterate` on x86 (32-bit): the instances

Untrusted: everything here is checked by Lean. The generic proofs
(`IterateCT.lean`, `HmacFinCT.lean`) at each hash function of `Hashes.lean`,
with the taint checks of their blocks, which the kernel evaluates for each
hash function, moved to the shared contracts of `Spec/Hmac/Generic.lean` and
`Spec/Pbkdf2/Generic.lean` (`sig_implies`), which the artifacts are emitted
with.
-/

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Hmac.Generic.X86 (finW finG iterW iterG countF)

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

/-- Memory holding the arguments `0x1000, 0x1400, 0, 0, 0x1800, 0x2000` of
`finalize` at `0x6004`. -/
def finMem : Mem := fun a =>
  if a = 0x6005 then 0x10 else if a = 0x6009 then 0x14 else if a = 0x6015 then 0x18 else
  if a = 0x6019 then 0x20 else 0

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes,
a digest of `D` bytes and `8 sc` bytes of scratch space, with the arguments
writable. -/
def finSat (S D sc : Nat) : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := finMem
  rd := [⟨0x1400, S⟩]
  wr := [⟨0x1000, S⟩, ⟨0x1800, D⟩, ⟨0x2000, 8 * sc⟩, ⟨0x6004, 24⟩]

theorem finSat_args (S D sc : Nat) :
    arg (finSat S D sc) 0 = 0x1000 ∧ arg (finSat S D sc) 1 = 0x1400 ∧ arg (finSat S D sc) 2 = 0 ∧
      arg (finSat S D sc) 3 = 0 ∧ arg (finSat S D sc) 4 = 0x1800 ∧ arg (finSat S D sc) 5 = 0x2000 ∧
      argAddr (finSat S D sc) 0 = 0x6004 ∧ (finSat S D sc).gpr .esp = 0x6000 := by
  have e : ∀ i, arg (finSat S D sc) i = arg (finSat 0 0 0) i := fun _ => rfl
  have e' : argAddr (finSat S D sc) 0 = argAddr (finSat 0 0 0) 0 := rfl
  rw [e, e, e, e, e, e, e']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> decide

/-! ## MD5 -/

theorem md5_iterChecks : Iterate.Checks md5M where
  pro := ⟨_, by taint_decide⟩
  load := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  tail := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem md5_finChecks : HmacFin.Checks md5M where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  out := ⟨_, by taint_decide⟩

theorem md5_iterImp : (iterW Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 80 16 48
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 80 16 48

theorem md5_finImp : (finW Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.finalizeContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 80 16 48
  sig_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 80 16 48

theorem md5_iterate : Verified X86.target md5M.iterate (Spec.Hmac.md5I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW md5Ok md5_iterChecks (by decide) md5_iterImp.sat_left).of_implies md5_iterImp

theorem md5_finalize : Verified X86.target md5M.hmacFin (Spec.Hmac.md5I.finalizeContract X86.abi 48) :=
  (HmacFin.verifiedW md5Ok md5_finChecks (by decide) md5_finImp.sat_left).of_implies md5_finImp

/-! ## SHA-1 -/

theorem sha1_iterChecks : Iterate.Checks sha1M where
  pro := ⟨_, by taint_decide⟩
  load := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  tail := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha1_finChecks : HmacFin.Checks sha1M where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  out := ⟨_, by taint_decide⟩

theorem sha1_iterImp : (iterW Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 84 20 56
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 84 20 56

theorem sha1_finImp : (finW Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.finalizeContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 84 20 56
  sig_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 84 20 56

theorem sha1_iterate : Verified X86.target sha1M.iterate (Spec.Hmac.sha1I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW sha1Ok sha1_iterChecks (by decide) sha1_iterImp.sat_left).of_implies sha1_iterImp

theorem sha1_finalize : Verified X86.target sha1M.hmacFin (Spec.Hmac.sha1I.finalizeContract X86.abi 48) :=
  (HmacFin.verifiedW sha1Ok sha1_finChecks (by decide) sha1_finImp.sat_left).of_implies sha1_finImp

/-! ## SHA-384 -/

theorem sha384_iterChecks : Iterate.Checks sha384M where
  pro := ⟨_, by taint_decide⟩
  load := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  tail := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha384_finChecks : HmacFin.Checks sha384M where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  out := ⟨_, by taint_decide⟩

theorem sha384_iterImp : (iterW Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 192 48 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 192 48 234

theorem sha384_finImp : (finW Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.finalizeContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 192 48 234
  sig_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 192 48 234

theorem sha384_iterate : Verified X86.target sha384M.iterate (Spec.Hmac.sha384I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW sha384Ok sha384_iterChecks (by decide) sha384_iterImp.sat_left).of_implies sha384_iterImp

theorem sha384_finalize : Verified X86.target sha384M.hmacFin (Spec.Hmac.sha384I.finalizeContract X86.abi 48) :=
  (HmacFin.verifiedW sha384Ok sha384_finChecks (by decide) sha384_finImp.sat_left).of_implies sha384_finImp

/-! ## SHA-512 -/

theorem sha512_iterChecks : Iterate.Checks sha512M' where
  pro := ⟨_, by taint_decide⟩
  load := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  tail := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_finChecks : HmacFin.Checks sha512M' where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  out := ⟨_, by taint_decide⟩

theorem sha512_iterImp : (iterW Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 192 64 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 192 64 234

theorem sha512_finImp : (finW Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.finalizeContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 192 64 234
  sig_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 192 64 234

theorem sha512_iterate : Verified X86.target sha512M'.iterate (Spec.Hmac.sha512I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW sha512Ok' sha512_iterChecks (by decide) sha512_iterImp.sat_left).of_implies sha512_iterImp

theorem sha512_finalize : Verified X86.target sha512M'.hmacFin (Spec.Hmac.sha512I.finalizeContract X86.abi 48) :=
  (HmacFin.verifiedW sha512Ok' sha512_finChecks (by decide) sha512_finImp.sat_left).of_implies sha512_finImp

/-! ## SHA-512/224 -/

theorem sha512_224_iterChecks : Iterate.Checks sha512_224M where
  pro := ⟨_, by taint_decide⟩
  load := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  tail := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_224_finChecks : HmacFin.Checks sha512_224M where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  out := ⟨_, by taint_decide⟩

theorem sha512_224_iterImp : (iterW Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 192 28 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 192 28 234

theorem sha512_224_finImp : (finW Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.finalizeContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 192 28 234
  sig_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 192 28 234

theorem sha512_224_iterate : Verified X86.target sha512_224M.iterate (Spec.Hmac.sha512_224I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW sha512_224Ok sha512_224_iterChecks (by decide) sha512_224_iterImp.sat_left).of_implies sha512_224_iterImp

theorem sha512_224_finalize : Verified X86.target sha512_224M.hmacFin (Spec.Hmac.sha512_224I.finalizeContract X86.abi 48) :=
  (HmacFin.verifiedW sha512_224Ok sha512_224_finChecks (by decide) sha512_224_finImp.sat_left).of_implies sha512_224_finImp

/-! ## SHA-512/256 -/

theorem sha512_256_iterChecks : Iterate.Checks sha512_256M where
  pro := ⟨_, by taint_decide⟩
  load := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  tail := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_256_finChecks : HmacFin.Checks sha512_256M where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  out := ⟨_, by taint_decide⟩

theorem sha512_256_iterImp : (iterW Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 192 32 234
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 192 32 234

theorem sha512_256_finImp : (finW Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.finalizeContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 192 32 234
  sig_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 192 32 234

theorem sha512_256_iterate : Verified X86.target sha512_256M.iterate (Spec.Hmac.sha512_256I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW sha512_256Ok sha512_256_iterChecks (by decide) sha512_256_iterImp.sat_left).of_implies sha512_256_iterImp

theorem sha512_256_finalize : Verified X86.target sha512_256M.hmacFin (Spec.Hmac.sha512_256I.finalizeContract X86.abi 48) :=
  (HmacFin.verifiedW sha512_256Ok sha512_256_finChecks (by decide) sha512_256_finImp.sat_left).of_implies sha512_256_finImp

end VG.Proof.Pbkdf2.Md.X86.Instances
