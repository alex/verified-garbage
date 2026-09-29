import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Pbkdf2.Generic.Arm.IterateCT
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Hashes

/-!
# PBKDF2-HMAC over the streaming hash functions on 32-bit ARM: the shared contracts

Untrusted: everything here is checked by Lean. As on AArch64
(`Proof/Pbkdf2/Generic/AArch64/Shared.lean`): the generic proof
(`IterateCT.lean`) at each hash function of
`Proof/Hmac/Generic/Arm/Hashes.lean`, moved to the shared contract of
`Spec/Pbkdf2/Generic.lean`, which the artifacts are emitted with.
-/

namespace VG.Proof.Pbkdf2.Generic.Arm.Shared

open VG.Arm
open VG.Proof.Hmac.Generic.Arm
open VG.Proof.Pbkdf2.Generic.Arm

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `8 sc` bytes of scratch space; `scratch`, at
`0x4000`, is the stack argument. -/
def iterSat (S D sc : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000
    | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x40 else 0
  rd := [⟨0x1000, 2 * S⟩, ⟨0x2000, D⟩, ⟨0x6000, 4⟩]
  wr := [⟨0x3000, D⟩, ⟨0x4000, 8 * sc⟩]

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

theorem sha1_imp : (iterG Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.iterateContract Arm.abi 16) := by
  contract_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, iterG, below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr]
    [iterSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using iterSat 84 20 56

theorem sha1 : Verified Arm.target (Impl.Pbkdf2.Generic.Arm.iterate sha1H)
    (Spec.Hmac.sha1I.iterateContract Arm.abi 16) :=
  (verified sha1OK sha1_checks (by decide) sha1_imp.sat_left).of_implies sha1_imp

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

theorem md5_imp : (iterG Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.iterateContract Arm.abi 16) := by
  contract_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, iterG, below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr]
    [iterSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using iterSat 80 16 48

theorem md5 : Verified Arm.target (Impl.Pbkdf2.Generic.Arm.iterate md5H)
    (Spec.Hmac.md5I.iterateContract Arm.abi 16) :=
  (verified md5OK md5_checks (by decide) md5_imp.sat_left).of_implies md5_imp

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

theorem sha384_imp : (iterG Spec.Hmac.sha384S 96).Implies (Spec.Hmac.sha384I.iterateContract Arm.abi 16) := by
  contract_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, iterG, below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr]
    [iterSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using iterSat 192 48 96

theorem sha384 : Verified Arm.target (Impl.Pbkdf2.Generic.Arm.iterate sha384H)
    (Spec.Hmac.sha384I.iterateContract Arm.abi 16) :=
  (verified sha384OK sha384_checks (by decide) sha384_imp.sat_left).of_implies sha384_imp

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

theorem sha512_imp : (iterG Spec.Hmac.sha512S 96).Implies (Spec.Hmac.sha512I.iterateContract Arm.abi 16) := by
  contract_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, iterG, below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr]
    [iterSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using iterSat 192 64 96

theorem sha512 : Verified Arm.target (Impl.Pbkdf2.Generic.Arm.iterate sha512H')
    (Spec.Hmac.sha512I.iterateContract Arm.abi 16) :=
  (verified sha512OK sha512_checks (by decide) sha512_imp.sat_left).of_implies sha512_imp

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

theorem sha512_224_imp : (iterG Spec.Hmac.sha512_224S 96).Implies (Spec.Hmac.sha512_224I.iterateContract Arm.abi 16) := by
  contract_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, iterG, below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr]
    [iterSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using iterSat 192 28 96

theorem sha512_224 : Verified Arm.target (Impl.Pbkdf2.Generic.Arm.iterate sha512_224H)
    (Spec.Hmac.sha512_224I.iterateContract Arm.abi 16) :=
  (verified sha512_224OK sha512_224_checks (by decide) sha512_224_imp.sat_left).of_implies sha512_224_imp

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

theorem sha512_256_imp : (iterG Spec.Hmac.sha512_256S 96).Implies (Spec.Hmac.sha512_256I.iterateContract Arm.abi 16) := by
  contract_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, iterG, below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr]
    [iterSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using iterSat 192 32 96

theorem sha512_256 : Verified Arm.target (Impl.Pbkdf2.Generic.Arm.iterate sha512_256H)
    (Spec.Hmac.sha512_256I.iterateContract Arm.abi 16) :=
  (verified sha512_256OK sha512_256_checks (by decide) sha512_256_imp.sat_left).of_implies sha512_256_imp

end VG.Proof.Pbkdf2.Generic.Arm.Shared
