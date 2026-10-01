import VerifiedGarbage.Proof.MlKem.X86_64.DcX

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_decaps_expanded` meets its contract

Untrusted: everything here is checked by Lean. The contract of `DcX.lean`
implies the shared one; its precondition holds of a state with the zero
decapsulation key and the expanded key of the zero encapsulation key in it
(`decapsXSat`, `expandedEk_ekxMem`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (ekxMem limMatrix expandedEk_ekxMem)

/-- The memory of `decapsXSat`: the expanded key of the zero encapsulation key at `0x4000`, and zeros
elsewhere (in particular the decapsulation key at `0x1000`). -/
noncomputable def decapsXSatMem : Mem :=
  ekxMem mlKem768 0x4000 (List.replicate 1184 0) (limMatrix 3 (ekRho mlKem768 (List.replicate 1184 0)))

theorem decapsXSatMem_ek : bytesAt decapsXSatMem (4096 + BitVec.ofNat 64 (384 * mlKem768.k)) mlKem768.ekLen =
    List.replicate 1184 0 := by
  refine bytesAt_ext (List.length_replicate ..) fun t ht => ?_
  have ht' : t < 1184 := ht
  have h : ¬ (4096 + BitVec.ofNat 64 (384 * mlKem768.k) + BitVec.ofNat 64 t - 0x4000).toNat < mlKem768.ekxLen := by
    show ¬ (4096 + BitVec.ofNat 64 1152 + BitVec.ofNat 64 t - 0x4000).toNat < 10432
    bv_omega
  simp only [decapsXSatMem, ekxMem, h, ite_false]
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt ht']
  rfl

theorem decapsXSatMem_pre : DecapsExpandedPre mlKem768 4096 16384 decapsXSatMem := by
  unfold DecapsExpandedPre
  rw [decapsXSatMem_ek]
  have h := expandedEk_ekxMem mlKem768 0x4000 (ek := List.replicate 1184 0) (List.length_replicate ..) (by decide)
    (by decide)
  exact h

/-- A state satisfying `decapsExpandedContract`'s precondition. -/
noncomputable def decapsXSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x4000 | .rdx => 0x7000 | .rcx => 0x8000 | .r8 => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := decapsXSatMem
  rd := [⟨0x1000, 2400⟩, ⟨0x4000, 10432⟩, ⟨0x7000, 1088⟩]
  wr := [⟨0x8000, 32⟩, ⟨0x10000, 32768⟩]

theorem decapsX_verified :
    Verified X86_64.target Impl.MlKem.X86_64.decapsX (Spec.MlKem.decapsExpandedContract X86_64.abi 32) :=
  Verified.of_correct decapsX_correct decapsX_ct
    { pre := by
        intro s h
        sig_pre [Spec.MlKem.decapsExpandedContract, Spec.MlKem.decapsExpandedSig, X86_64.abi, VG.X86_64.argRegs] at h
        exact h.2
      post := by
        intro s s' _ h
        sig_post [Spec.MlKem.decapsExpandedContract, Spec.MlKem.decapsExpandedSig, decapsXK, X86_64.abi,
          VG.X86_64.argRegs]
        exact h
      pub := by sig_implies_pub [Spec.MlKem.decapsExpandedContract, Spec.MlKem.decapsExpandedSig, decapsXK,
        X86_64.abi, VG.X86_64.argRegs]
      sat := by
        refine ⟨decapsXSat, ?_⟩
        sig_pre [Spec.MlKem.decapsExpandedContract, Spec.MlKem.decapsExpandedSig, X86_64.abi, VG.X86_64.argRegs]
        sig_and_intros
        all_goals first
          | with_reducible exact decapsXSatMem_pre
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

end VG.Proof.MlKem.X86_64
