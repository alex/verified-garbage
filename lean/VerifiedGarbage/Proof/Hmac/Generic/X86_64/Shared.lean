import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.InitCT
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.FinalizeCT
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Hashes

/-!
# HMAC over the streaming hash functions on x86-64: the shared contracts

Untrusted: everything here is checked by Lean. The generic proofs
(`InitCT.lean`, `FinalizeCT.lean`) at each hash function of `Hashes.lean`:
the kernel checks the pieces of code between calls with the taint analysis,
and that the code never loads MXCSR, and the proofs move to the shared
contracts of `Spec/Hmac/Generic.lean`, which the artifacts are emitted with.
-/

namespace VG.Proof.Hmac.Generic.X86_64.Shared

open VG.X86_64
open VG.Proof.Hmac.Generic.X86_64

/-- A state satisfying `init`'s precondition, with states of `S` bytes and
`8 sc` bytes of scratch space (and a one-byte key). -/
def initSat (S sc : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rdx => 0x30000 | .rcx => 1 | .r8 => 0x40000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x30000, 1⟩]
  wr := [⟨0x10000, S⟩, ⟨0x20000, S⟩, ⟨0x40000, 8 * sc⟩]

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes,
a digest of `D` bytes and `8 sc` bytes of scratch space. -/
def finSat (S D sc : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rcx => 0x30000 | .r8 => 0x40000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x20000, S⟩]
  wr := [⟨0x10000, S⟩, ⟨0x30000, D⟩, ⟨0x40000, 8 * sc⟩]

/-! ## SHA-1 -/

theorem sha1_initChecks : Init.Checks sha1H where
  keys := ⟨_, by taint_decide⟩
  argI := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  argU₁ := ⟨_, by taint_decide⟩
  argU₂ := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha1_finChecks : Finalize.Checks sha1H where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  copy1 := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin2 := ⟨_, by taint_decide⟩
  copy2 := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha1_initImp : (initG Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.initContract X86_64.abi 16) := by
  contract_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, initG, X86_64.abi, X86_64.argRegs]
    [initSat] using initSat 84 56

theorem sha1_finImp : (finG Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.finalizeContract X86_64.abi 16) := by
  contract_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, finG, X86_64.abi, X86_64.argRegs]
    [finSat] using finSat 84 20 56

theorem sha1_init : Verified X86_64.target sha1H.init (Spec.Hmac.sha1I.initContract X86_64.abi 16) :=
  (Init.verified sha1OK sha1_initChecks (by decide) (by decide +kernel) sha1_initImp.sat_left).of_implies
    sha1_initImp

theorem sha1_finalize : Verified X86_64.target sha1H.finalize (Spec.Hmac.sha1I.finalizeContract X86_64.abi 16) :=
  (Finalize.verified sha1OK sha1_finChecks (by decide) (by decide +kernel) sha1_finImp.sat_left).of_implies
    sha1_finImp

/-! ## MD5 -/

theorem md5_initChecks : Init.Checks md5H where
  keys := ⟨_, by taint_decide⟩
  argI := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  argU₁ := ⟨_, by taint_decide⟩
  argU₂ := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem md5_finChecks : Finalize.Checks md5H where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  copy1 := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin2 := ⟨_, by taint_decide⟩
  copy2 := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem md5_initImp : (initG Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.initContract X86_64.abi 16) := by
  contract_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, initG, X86_64.abi, X86_64.argRegs]
    [initSat] using initSat 80 48

theorem md5_finImp : (finG Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.finalizeContract X86_64.abi 16) := by
  contract_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, finG, X86_64.abi, X86_64.argRegs]
    [finSat] using finSat 80 16 48

theorem md5_init : Verified X86_64.target md5H.init (Spec.Hmac.md5I.initContract X86_64.abi 16) :=
  (Init.verified md5OK md5_initChecks (by decide) (by decide +kernel) md5_initImp.sat_left).of_implies
    md5_initImp

theorem md5_finalize : Verified X86_64.target md5H.finalize (Spec.Hmac.md5I.finalizeContract X86_64.abi 16) :=
  (Finalize.verified md5OK md5_finChecks (by decide) (by decide +kernel) md5_finImp.sat_left).of_implies
    md5_finImp

/-! ## SHA-384 -/

theorem sha384_initChecks : Init.Checks sha384H where
  keys := ⟨_, by taint_decide⟩
  argI := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  argU₁ := ⟨_, by taint_decide⟩
  argU₂ := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha384_finChecks : Finalize.Checks sha384H where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  copy1 := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin2 := ⟨_, by taint_decide⟩
  copy2 := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha384_initImp : (initG Spec.Hmac.sha384S 96).Implies (Spec.Hmac.sha384I.initContract X86_64.abi 16) := by
  contract_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, initG, X86_64.abi, X86_64.argRegs]
    [initSat] using initSat 192 96

theorem sha384_finImp : (finG Spec.Hmac.sha384S 96).Implies (Spec.Hmac.sha384I.finalizeContract X86_64.abi 16) := by
  contract_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, finG, X86_64.abi, X86_64.argRegs]
    [finSat] using finSat 192 48 96

theorem sha384_init : Verified X86_64.target sha384H.init (Spec.Hmac.sha384I.initContract X86_64.abi 16) :=
  (Init.verified sha384OK sha384_initChecks (by decide) (by decide +kernel) sha384_initImp.sat_left).of_implies
    sha384_initImp

theorem sha384_finalize : Verified X86_64.target sha384H.finalize (Spec.Hmac.sha384I.finalizeContract X86_64.abi 16) :=
  (Finalize.verified sha384OK sha384_finChecks (by decide) (by decide +kernel) sha384_finImp.sat_left).of_implies
    sha384_finImp

/-! ## SHA-512 -/

theorem sha512_initChecks : Init.Checks sha512H' where
  keys := ⟨_, by taint_decide⟩
  argI := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  argU₁ := ⟨_, by taint_decide⟩
  argU₂ := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_finChecks : Finalize.Checks sha512H' where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  copy1 := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin2 := ⟨_, by taint_decide⟩
  copy2 := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_initImp : (initG Spec.Hmac.sha512S 96).Implies (Spec.Hmac.sha512I.initContract X86_64.abi 16) := by
  contract_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, initG, X86_64.abi, X86_64.argRegs]
    [initSat] using initSat 192 96

theorem sha512_finImp : (finG Spec.Hmac.sha512S 96).Implies (Spec.Hmac.sha512I.finalizeContract X86_64.abi 16) := by
  contract_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, finG, X86_64.abi, X86_64.argRegs]
    [finSat] using finSat 192 64 96

theorem sha512_init : Verified X86_64.target sha512H'.init (Spec.Hmac.sha512I.initContract X86_64.abi 16) :=
  (Init.verified sha512OK sha512_initChecks (by decide) (by decide +kernel) sha512_initImp.sat_left).of_implies
    sha512_initImp

theorem sha512_finalize : Verified X86_64.target sha512H'.finalize (Spec.Hmac.sha512I.finalizeContract X86_64.abi 16) :=
  (Finalize.verified sha512OK sha512_finChecks (by decide) (by decide +kernel) sha512_finImp.sat_left).of_implies
    sha512_finImp

/-! ## SHA-512/224 -/

theorem sha512_224_initChecks : Init.Checks sha512_224H where
  keys := ⟨_, by taint_decide⟩
  argI := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  argU₁ := ⟨_, by taint_decide⟩
  argU₂ := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_224_finChecks : Finalize.Checks sha512_224H where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  copy1 := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin2 := ⟨_, by taint_decide⟩
  copy2 := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_224_initImp : (initG Spec.Hmac.sha512_224S 96).Implies (Spec.Hmac.sha512_224I.initContract X86_64.abi 16) := by
  contract_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, initG, X86_64.abi, X86_64.argRegs]
    [initSat] using initSat 192 96

theorem sha512_224_finImp : (finG Spec.Hmac.sha512_224S 96).Implies (Spec.Hmac.sha512_224I.finalizeContract X86_64.abi 16) := by
  contract_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, finG, X86_64.abi, X86_64.argRegs]
    [finSat] using finSat 192 28 96

theorem sha512_224_init : Verified X86_64.target sha512_224H.init (Spec.Hmac.sha512_224I.initContract X86_64.abi 16) :=
  (Init.verified sha512_224OK sha512_224_initChecks (by decide) (by decide +kernel) sha512_224_initImp.sat_left).of_implies
    sha512_224_initImp

theorem sha512_224_finalize : Verified X86_64.target sha512_224H.finalize (Spec.Hmac.sha512_224I.finalizeContract X86_64.abi 16) :=
  (Finalize.verified sha512_224OK sha512_224_finChecks (by decide) (by decide +kernel) sha512_224_finImp.sat_left).of_implies
    sha512_224_finImp

/-! ## SHA-512/256 -/

theorem sha512_256_initChecks : Init.Checks sha512_256H where
  keys := ⟨_, by taint_decide⟩
  argI := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  argU₁ := ⟨_, by taint_decide⟩
  argU₂ := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_256_finChecks : Finalize.Checks sha512_256H where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  copy1 := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin2 := ⟨_, by taint_decide⟩
  copy2 := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_256_initImp : (initG Spec.Hmac.sha512_256S 96).Implies (Spec.Hmac.sha512_256I.initContract X86_64.abi 16) := by
  contract_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, initG, X86_64.abi, X86_64.argRegs]
    [initSat] using initSat 192 96

theorem sha512_256_finImp : (finG Spec.Hmac.sha512_256S 96).Implies (Spec.Hmac.sha512_256I.finalizeContract X86_64.abi 16) := by
  contract_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, finG, X86_64.abi, X86_64.argRegs]
    [finSat] using finSat 192 32 96

theorem sha512_256_init : Verified X86_64.target sha512_256H.init (Spec.Hmac.sha512_256I.initContract X86_64.abi 16) :=
  (Init.verified sha512_256OK sha512_256_initChecks (by decide) (by decide +kernel) sha512_256_initImp.sat_left).of_implies
    sha512_256_initImp

theorem sha512_256_finalize : Verified X86_64.target sha512_256H.finalize (Spec.Hmac.sha512_256I.finalizeContract X86_64.abi 16) :=
  (Finalize.verified sha512_256OK sha512_256_finChecks (by decide) (by decide +kernel) sha512_256_finImp.sat_left).of_implies
    sha512_256_finImp

end VG.Proof.Hmac.Generic.X86_64.Shared
