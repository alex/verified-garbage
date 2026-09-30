import VerifiedGarbage.Proof.MlKem.X86_64.EcX

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_encaps_expanded` meets its contract

Untrusted: everything here is checked by Lean. The contract of `EcX.lean`
implies the shared one; its precondition holds of a state with the expanded
key of the zero encapsulation key (`encapsXSat`, `expandedEk_ekxMem`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (ekxMem limMatrix expandedEk_ekxMem)

/-- The memory of `encapsXSat`: the expanded key of the zero encapsulation key at `0x1000`. -/
noncomputable def encapsXSatMem : Mem :=
  ekxMem mlKem768 0x1000 (List.replicate 1184 0) (limMatrix 3 (ekRho mlKem768 (List.replicate 1184 0)))

theorem encapsXSatMem_ekx : ExpandedEk mlKem768 encapsXSatMem 4096 (bytesAt encapsXSatMem 4096 1184) := by
  have h := expandedEk_ekxMem mlKem768 0x1000 (ek := List.replicate 1184 0) (List.length_replicate ..) (by decide)
    (by decide)
  have e : bytesAt encapsXSatMem 0x1000 1184 = List.replicate 1184 0 := h.1
  rw [e]
  exact h

/-- A state satisfying `encapsExpandedContract`'s precondition. -/
noncomputable def encapsXSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x4000 | .rdx => 0x5000 | .rcx => 0x6000 | .r8 => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := encapsXSatMem
  rd := [⟨0x1000, 10432⟩, ⟨0x4000, 32⟩]
  wr := [⟨0x5000, 32⟩, ⟨0x6000, 1088⟩, ⟨0x10000, 32768⟩]

theorem encapsX_verified :
    Verified X86_64.target Impl.MlKem.X86_64.encapsX (Spec.MlKem.encapsExpandedContract X86_64.abi 32) :=
  Verified.of_correct encapsX_correct encapsX_ct
    { pre := by
        intro s h
        sig_pre [Spec.MlKem.encapsExpandedContract, Spec.MlKem.encapsExpandedSig, X86_64.abi, VG.X86_64.argRegs] at h
        exact h.2
      post := by
        intro s s' _ h
        sig_post [Spec.MlKem.encapsExpandedContract, Spec.MlKem.encapsExpandedSig, encapsXK, X86_64.abi,
          VG.X86_64.argRegs]
        exact h
      pub := by sig_implies_pub [Spec.MlKem.encapsExpandedContract, Spec.MlKem.encapsExpandedSig, encapsXK,
        X86_64.abi, VG.X86_64.argRegs]
      sat := by
        refine ⟨encapsXSat, ?_⟩
        sig_pre [Spec.MlKem.encapsExpandedContract, Spec.MlKem.encapsExpandedSig, X86_64.abi, VG.X86_64.argRegs]
        sig_and_intros
        all_goals first
          | with_reducible exact encapsXSatMem_ekx
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

end VG.Proof.MlKem.X86_64
