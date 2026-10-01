import VerifiedGarbage.Proof.MlKem1024.X86_64.DcX

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_decaps_expanded` meets its contract

Untrusted: everything here is checked by Lean. The contract of `DcX.lean`
implies the shared one; its precondition holds of a state with the zero
decapsulation key and the expanded key of the zero encapsulation key in it
(`decapsX1024Sat`, `expandedEk_ekxMem`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (ekxMem limMatrix expandedEk_ekxMem)

/-- The memory of `decapsX1024Sat`: the expanded key of the zero encapsulation key at `0x4000`, and zeros
elsewhere (in particular the decapsulation key at `0x1000`). -/
noncomputable def decapsX1024SatMem : Mem :=
  ekxMem mlKem1024 0x4000 (List.replicate 1568 0) (limMatrix 4 (ekRho mlKem1024 (List.replicate 1568 0)))

theorem decapsX1024SatMem_ek : bytesAt decapsX1024SatMem (4096 + BitVec.ofNat 64 (384 * mlKem1024.k)) mlKem1024.ekLen =
    List.replicate 1568 0 := by
  refine bytesAt_ext (List.length_replicate ..) fun t ht => ?_
  have ht' : t < 1568 := ht
  have h : ¬ (4096 + BitVec.ofNat 64 (384 * mlKem1024.k) + BitVec.ofNat 64 t - 0x4000).toNat < mlKem1024.ekxLen := by
    show ¬ (4096 + BitVec.ofNat 64 1536 + BitVec.ofNat 64 t - 0x4000).toNat < 17984
    bv_omega
  simp only [decapsX1024SatMem, ekxMem, h, ite_false]
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt ht']
  rfl

theorem decapsX1024SatMem_pre : DecapsExpandedPre mlKem1024 4096 16384 decapsX1024SatMem := by
  unfold DecapsExpandedPre
  rw [decapsX1024SatMem_ek]
  have h := expandedEk_ekxMem mlKem1024 0x4000 (ek := List.replicate 1568 0) (List.length_replicate ..) (by decide)
    (by decide)
  exact h

/-- A state satisfying `decapsExpandedContract`'s precondition. -/
noncomputable def decapsX1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x4000 | .rdx => 0x9000 | .rcx => 0xA000 | .r8 => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := decapsX1024SatMem
  rd := [⟨0x1000, 3168⟩, ⟨0x4000, 17984⟩, ⟨0x9000, 1568⟩]
  wr := [⟨0xA000, 32⟩, ⟨0x10000, 49152⟩]

theorem decapsX1024_verified :
    Verified X86_64.target Impl.MlKem1024.X86_64.decapsX1024 (Spec.MlKem1024.decapsExpandedContract X86_64.abi 32) :=
  Verified.of_correct decapsX1024_correct decapsX1024_ct
    { pre := by
        intro s h
        sig_pre [Spec.MlKem1024.decapsExpandedContract, Spec.MlKem1024.decapsExpandedSig, X86_64.abi, VG.X86_64.argRegs] at h
        exact h.2
      post := by
        intro s s' _ h
        sig_post [Spec.MlKem1024.decapsExpandedContract, Spec.MlKem1024.decapsExpandedSig, decapsX1024K, X86_64.abi,
          VG.X86_64.argRegs]
        exact h
      pub := by sig_implies_pub [Spec.MlKem1024.decapsExpandedContract, Spec.MlKem1024.decapsExpandedSig, decapsX1024K,
        X86_64.abi, VG.X86_64.argRegs]
      sat := by
        refine ⟨decapsX1024Sat, ?_⟩
        sig_pre [Spec.MlKem1024.decapsExpandedContract, Spec.MlKem1024.decapsExpandedSig, X86_64.abi, VG.X86_64.argRegs]
        sig_and_intros
        all_goals first
          | with_reducible exact decapsX1024SatMem_pre
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

end VG.Proof.MlKem1024.X86_64
