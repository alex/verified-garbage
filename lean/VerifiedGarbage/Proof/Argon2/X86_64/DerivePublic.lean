import VerifiedGarbage.Proof.Argon2.X86_64.DeriveAbi

/-! The public entry-point relation reads u32 arguments at their declared width. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure AbiPublic (s t : State) : Prop where
  sp : s.gpr .rsp = t.gpr .rsp
  regs : ∀ r ∈ [.rsi, .rdx, .rcx, .r8], s.gpr r = t.gpr r
  smallRegs : ∀ r ∈ [.rdi, .r9], (s.gpr r).setWidth 32 = (t.gpr r).setWidth 32
  smallWords : ∀ d ∈ [8, 16, 24], (abiWord s d).setWidth 32 = (abiWord t d).setWidth 32
  words : ∀ d ∈ [32, 40, 48, 56, 64, 72, 80, 88, 96], abiWord s d = abiWord t d
  references : Spec.Argon2.references (abiParams s)
      (Spec.Blake2.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
      (Spec.Blake2.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
      (Spec.Blake2.bytesAt s.mem (abiWord s 32) (abiWord s 40).toNat)
      (Spec.Blake2.bytesAt s.mem (abiWord s 48) (abiWord s 56).toNat) =
    Spec.Argon2.references (abiParams t)
      (Spec.Blake2.bytesAt t.mem (t.gpr .rsi) (t.gpr .rdx).toNat)
      (Spec.Blake2.bytesAt t.mem (t.gpr .rcx) (t.gpr .r8).toNat)
      (Spec.Blake2.bytesAt t.mem (abiWord t 32) (abiWord t 40).toNat)
      (Spec.Blake2.bytesAt t.mem (abiWord t 48) (abiWord t 56).toNat)

theorem abi_public (s t : State) (h : (Spec.Argon2.deriveContract X86_64.abi 344).pub s t) :
    AbiPublic s t := by
  sig_pub [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  sig_split h
  constructor
  all_goals sig_eval [abiWord, abiParams]
  all_goals sig_and_intros
  all_goals sig_close
  all_goals with_reducible assumption

theorem AbiPublic.params {s t : State} (h : AbiPublic s t) : abiParams s = abiParams t := by
  unfold abiParams
  rw [h.smallRegs .rdi (by simp), h.smallRegs .r9 (by simp),
    h.smallWords 8 (by simp), h.smallWords 16 (by simp), h.words 96 (by simp)]

end VG.Proof.Argon2.X86_64.Derive
