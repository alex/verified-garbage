import VerifiedGarbage.Proof.Argon2.AArch64.DeriveAbi

/-! The public entry-point relation reads u32 arguments at their declared width. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

structure AbiPublic (s t : State) : Prop where
  sp : s.sp = t.sp
  regs : ∀ r ∈ [.x1, .x2, .x3, .x4], s.gpr r = t.gpr r
  smallRegs : ∀ r ∈ [.x0, .x5, .x6, .x7], (s.gpr r).setWidth 32 = (t.gpr r).setWidth 32
  smallWords : ∀ d ∈ [0], (abiWord s d).setWidth 32 = (abiWord t d).setWidth 32
  words : ∀ d ∈ [8, 16, 24, 32, 40, 48, 56, 64, 72], abiWord s d = abiWord t d
  references : Spec.Argon2.references (abiParams s)
      (Spec.Blake2.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
      (Spec.Blake2.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
      (Spec.Blake2.bytesAt s.mem (abiWord s 8) (abiWord s 16).toNat)
      (Spec.Blake2.bytesAt s.mem (abiWord s 24) (abiWord s 32).toNat) =
    Spec.Argon2.references (abiParams t)
      (Spec.Blake2.bytesAt t.mem (t.gpr .x1) (t.gpr .x2).toNat)
      (Spec.Blake2.bytesAt t.mem (t.gpr .x3) (t.gpr .x4).toNat)
      (Spec.Blake2.bytesAt t.mem (abiWord t 8) (abiWord t 16).toNat)
      (Spec.Blake2.bytesAt t.mem (abiWord t 24) (abiWord t 32).toNat)

theorem abi_public (s t : State) (h : (Spec.Argon2.deriveContract AArch64.abi 400).pub s t) :
    AbiPublic s t := by
  sig_pub [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, AArch64.abi,
    AArch64.argRegs, AArch64.firstNarrowStack, AArch64.stackArg, AArch64.stackArgAddr, List.range, List.range.loop] at h
  all_goals simp only [BitVec.add_zero] at *
  sig_split h
  constructor
  all_goals sig_eval [abiWord, abiParams]
  all_goals try simp only [BitVec.add_zero]
  all_goals sig_and_intros
  all_goals sig_close
  all_goals with_reducible assumption

theorem AbiPublic.params {s t : State} (h : AbiPublic s t) : abiParams s = abiParams t := by
  unfold abiParams
  rw [h.smallRegs .x0 (by simp), h.smallRegs .x5 (by simp),
    h.smallRegs .x6 (by simp), h.smallRegs .x7 (by simp), h.words 72 (by simp)]

end VG.Proof.Argon2.AArch64.Derive
