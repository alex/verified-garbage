import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit

/-!
# ML-DSA on AArch64: `vg_mldsa_simple_bit_pack`

Untrusted: everything here is checked by Lean. The loop is proven once for
every width (`packLoop_ok`), and the function by its three cases, which the
length chooses.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only wp_ldrw wp_nil toNat_readW32 abi_of agree_of)
open VG.Proof.MlDsa.Pack

theorem sbpLd_ok (K12 K13 : BitVec 64) : LdOk sbpLd BitVec.toNat K12 K13 := fun j _ _ _ hj hin =>
  wp_ldrw ⟨by omega, by omega⟩ rfl hin fun _ o₁ e₁ => wp_nil ⟨by rw [e₁, toNat_readW32], o₁.mono⟩

/-- A value at most `b` is less than `2 ^ bitlen b`. -/
theorem lt_bitlen {x b : Nat} (h : x ≤ b) : x < 2 ^ bitlen b := Nat.lt_of_le_of_lt h Nat.lt_log2_self

/-- The bound and the width, by the length. -/
theorem sbp_cases {b len : Nat} (hb : b ∈ simpleBitPackBounds) (hlen : len = 32 * bitlen b) :
    (b = 15 ∧ bitlen b = 4 ∧ len = 128) ∨ (b = 43 ∧ bitlen b = 6 ∧ len = 192) ∨
      (b = 1023 ∧ bitlen b = 10 ∧ len = 320) := by
  simp only [simpleBitPackBounds, t1Max_eq, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact .inr (.inr ⟨rfl, rfl, hlen⟩)
  · exact .inr (.inl ⟨rfl, rfl, hlen⟩)
  · exact .inl ⟨rfl, rfl, hlen⟩

theorem sbp_wp {s₀ : State} (hp : simpleBitPackK.pre s₀) :
    WP isa Impl.MlDsa.AArch64.Pack.simpleBitPack s₀ fun s' => simpleBitPackK.post s₀ s' := by
  obtain ⟨hrd, hwr, hsep, hb, hlen, hle⟩ := hp
  have go : ∀ {d c nb : Nat}, Shape d c nb → bitlen (wArg s₀ .x1) = d → ∀ s : State, Only [.x9] s₀ s →
      WP isa (packLoop sbpLd d c nb) s fun s' => simpleBitPackK.post s₀ s' := by
    intro d c nb hs hd s o
    rw [hd] at hlen
    refine WP.mono (packLoop_ok (sbpLd_ok (s.gpr .x12) (s.gpr .x13)) hs (f := s₀.gpr .x0) (o := s₀.gpr .x2)
      (s₀ := s₀) (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hwr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hsep)
      (fun i hi => by rw [← hd]; exact lt_bitlen (hle i hi)) (o.get .x0) (o.get .x2) rfl rfl o.rd o.wr o.mem)
      fun s' ⟨hB, _, _⟩ => ?_
    show bytesAt s'.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat = simpleBitPack _ _
    rw [hlen, hB, simpleBitPack_eq, natPolyAt_toList, hd]
  have hc := sbp_cases hb hlen
  unfold Impl.MlDsa.AArch64.Pack.simpleBitPack
  refine sel_ok (by decide) (fun s₁ o₁ h => ?_) (fun s₁ o₁ h => ?_)
  · have e : bitlen (wArg s₀ .x1) = 4 := by omega
    exact go (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e s₁ o₁
  refine sel_ok (by decide) (fun s₂ o₂ h' => ?_) (fun s₂ o₂ h' => ?_)
  · have e : bitlen (wArg s₀ .x1) = 6 := by rw [o₁.get .x3] at h'; omega
    exact go (d := 6) (c := 4) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e s₂ (o₁.trans o₂).mono
  · have e : bitlen (wArg s₀ .x1) = 10 := by rw [o₁.get .x3] at h'; omega
    exact go (d := 10) (c := 4) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e s₂ (o₁.trans o₂).mono

theorem simpleBitPack_correct (s : State) (hs : simpleBitPackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Pack.simpleBitPack s t s' ∧ abiPreserved s s' ∧
      simpleBitPackK.post s s' := by
  obtain ⟨t, s', he, hb⟩ := sbp_wp hs
  exact ⟨t, s', he, abi_of rfl (by lit_decide) he, hb⟩

theorem simpleBitPack_ct :
    ConstantTime isa simpleBitPackK.pre simpleBitPackK.pub Impl.MlDsa.AArch64.Pack.simpleBitPack :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h2, h3, hsp⟩ => agree_of hsp (by simp [h0, h2, h3])) (by taint_decide)

/-- A state satisfying the precondition. -/
def simpleBitPackSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 15 | .x2 => 0x2000 | .x3 => 128 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 128⟩]

theorem simpleBitPack_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Pack.simpleBitPack (simpleBitPackContract AArch64.abi) :=
  Verified.of_correct simpleBitPack_correct simpleBitPack_ct
    { pre := by sig_implies_pre [simpleBitPackContract, simpleBitPackSig, simpleBitPackK, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [simpleBitPackContract, simpleBitPackSig, simpleBitPackK, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [simpleBitPackContract, simpleBitPackSig, simpleBitPackK, AArch64.abi,
        AArch64.argRegs]
      sat := by
        refine ⟨simpleBitPackSat, ?_⟩
        sig_pre [simpleBitPackContract, simpleBitPackSig, AArch64.abi, AArch64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | exact fun i _ => by rw [coeffAt_zero]; exact Nat.zero_le _
          | (simp only [simpleBitPackBounds, t1Max_eq]; decide)
          | decide }

end VG.Proof.MlDsa.AArch64.Pack
