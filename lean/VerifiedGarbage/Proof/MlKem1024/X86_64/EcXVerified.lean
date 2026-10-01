import VerifiedGarbage.Proof.MlKem1024.X86_64.EcX

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_encaps_expanded` meets its contract

Untrusted: everything here is checked by Lean. The contract of `EcX.lean`
implies the shared one; its precondition holds of a state with the expanded
key of the zero encapsulation key (`encapsX1024Sat`, `expandedEk_ekxMem`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (ekxMem limMatrix expandedEk_ekxMem)

/-- The memory of `encapsX1024Sat`: the expanded key of the zero encapsulation key at `0x1000`. -/
noncomputable def encapsX1024SatMem : Mem :=
  ekxMem mlKem1024 0x1000 (List.replicate 1568 0) (limMatrix 4 (ekRho mlKem1024 (List.replicate 1568 0)))

theorem encapsX1024SatMem_ekx : ExpandedEk mlKem1024 encapsX1024SatMem 4096 (bytesAt encapsX1024SatMem 4096 1568) := by
  have h := expandedEk_ekxMem mlKem1024 0x1000 (ek := List.replicate 1568 0) (List.length_replicate ..) (by decide)
    (by decide)
  have e : bytesAt encapsX1024SatMem 0x1000 1568 = List.replicate 1568 0 := h.1
  rw [e]
  exact h

/-- A state satisfying `encapsExpandedContract`'s precondition. -/
noncomputable def encapsX1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x6000 | .rdx => 0x7000 | .rcx => 0x8000 | .r8 => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := encapsX1024SatMem
  rd := [⟨0x1000, 17984⟩, ⟨0x6000, 32⟩]
  wr := [⟨0x7000, 32⟩, ⟨0x8000, 1568⟩, ⟨0x10000, 49152⟩]

theorem encapsX1024_verified :
    Verified X86_64.target Impl.MlKem1024.X86_64.encapsX1024 (Spec.MlKem1024.encapsExpandedContract X86_64.abi 32) :=
  Verified.of_correct encapsX1024_correct encapsX1024_ct
    { pre := by
        intro s h
        sig_pre [Spec.MlKem1024.encapsExpandedContract, Spec.MlKem1024.encapsExpandedSig, X86_64.abi, VG.X86_64.argRegs] at h
        exact h.2
      post := by
        intro s s' _ h
        sig_post [Spec.MlKem1024.encapsExpandedContract, Spec.MlKem1024.encapsExpandedSig, encapsX1024K, X86_64.abi,
          VG.X86_64.argRegs]
        exact h
      pub := by sig_implies_pub [Spec.MlKem1024.encapsExpandedContract, Spec.MlKem1024.encapsExpandedSig, encapsX1024K,
        X86_64.abi, VG.X86_64.argRegs]
      sat := by
        refine ⟨encapsX1024Sat, ?_⟩
        sig_pre [Spec.MlKem1024.encapsExpandedContract, Spec.MlKem1024.encapsExpandedSig, X86_64.abi, VG.X86_64.argRegs]
        sig_and_intros
        all_goals first
          | with_reducible exact encapsX1024SatMem_ekx
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

end VG.Proof.MlKem1024.X86_64
