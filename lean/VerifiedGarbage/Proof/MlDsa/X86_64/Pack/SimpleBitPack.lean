import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Loop
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Contracts
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on x86-64: `vg_mldsa_simple_bit_pack`

Untrusted: everything here is checked by Lean. The loop is proven once for
every width (`packLoop_ok`), and the function by its three cases.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep retR pR dArg regsLo agree_regsLo
  gprPreserved_of toNat_setWidth64 read_zero)
open VG.Proof.MlDsa.Pack

theorem sbpLd_ok : LdOk sbpLd BitVec.toNat := fun j s hin => by
  refine WP.keep _ ?_ (by rfl)
  unfold sbpLd
  xrun [ea_at', hin]
  rw [toNat_setWidth64]

/-- A value at most `b` is less than `2 ^ bitlen b`. -/
theorem lt_bitlen {x b : Nat} (h : x ≤ b) : x < 2 ^ bitlen b := Nat.lt_of_le_of_lt h Nat.lt_log2_self

theorem sbpPro_ok (s : State) :
    WP isa (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx)]) s fun s' =>
      (dArg s' .rsi = dArg s .rsi ∧ s'.gpr .r8 = s.gpr .rdx ∧ s'.mem = s.mem) ∧ Keep [.rsi, .r8] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [dArg]

theorem sbp_wp {s₀ : State} (hp : simpleBitPackK.pre s₀) :
    WP isa Impl.MlDsa.X86_64.Pack.simpleBitPack s₀ fun s' =>
      simpleBitPackK.post s₀ s' ∧ Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  obtain ⟨hrd, hwr, hsep, -, -, hb, hlen, hle⟩ := hp
  have go : ∀ {d c nb : Nat}, Shape d c nb → bitlen (dArg s₀ .rsi) = d → ∀ s : State,
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .r8 = s₀.gpr .rdx → s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (packLoop sbpLd d c nb) s fun s' =>
        simpleBitPackK.post s₀ s' ∧ Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
    intro d c nb hs hd s h1 h2 h3 h4 h5
    rw [hd] at hlen
    refine WP.mono (packLoop_ok sbpLd_ok hs (f := s₀.gpr .rdi) (o := s₀.gpr .rdx) (s₀ := s₀)
      (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hwr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hsep)
      (fun i hi => by rw [← hd]; exact lt_bitlen (hle i hi)) h1 h2 h3 h4 h5)
      fun s' ⟨hB, hf, _⟩ => ⟨?_, by rw [hlen]; exact hf⟩
    show bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = simpleBitPack _ _
    rw [hlen, hB, simpleBitPack_eq, natPolyAt_toList, hd]
  unfold Impl.MlDsa.X86_64.Pack.simpleBitPack
  refine WP.seq (WP.mono (sbpPro_ok s₀) fun s₁ ⟨⟨si₁, r8₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  refine sel_ok .rsi 15 _ _ s₁ (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_) (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_)
  · have e : dArg s₀ .rsi = 15 := by rw [← si₁, lo_of_eq h]
    exact go (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by rw [e]; decide) s₂
      (by rw [g₂, di₁]) (by rw [g₂, r8₁]) (by rw [rd₂, k₁.2.1]) (by rw [wr₂, k₁.2.2]) (by rw [m₂, m₁])
  have n15 : dArg s₀ .rsi ≠ 15 := by rw [← si₁]; exact lo_ne h
  have ds₂ : dArg s₂ .rsi = dArg s₀ .rsi := by unfold dArg; rw [g₂]; exact si₁
  refine sel_ok .rsi 43 _ _ s₂ (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_) (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_)
  · have e : dArg s₀ .rsi = 43 := by rw [← ds₂, lo_of_eq h]
    exact go (d := 6) (c := 4) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by rw [e]; decide) s₃
      (by rw [g₃, g₂, di₁]) (by rw [g₃, g₂, r8₁]) (by rw [rd₃, rd₂, k₁.2.1]) (by rw [wr₃, wr₂, k₁.2.2])
      (by rw [m₃, m₂, m₁])
  · have n43 : dArg s₀ .rsi ≠ 43 := by rw [← ds₂]; exact lo_ne h
    have e : dArg s₀ .rsi = 1023 := by
      simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with e | e | e
      · exact e
      · exact absurd e n43
      · exact absurd e n15
    exact go (d := 10) (c := 4) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by rw [e]; decide) s₃
      (by rw [g₃, g₂, di₁]) (by rw [g₃, g₂, r8₁]) (by rw [rd₃, rd₂, k₁.2.1]) (by rw [wr₃, wr₂, k₁.2.2])
      (by rw [m₃, m₂, m₁])

theorem simpleBitPack_correct (s : State) (hs : simpleBitPackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Pack.simpleBitPack s t s' ∧ abiPreserved s s' ∧
      simpleBitPackK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Pack.simpleBitPack)
    [.rax, .rcx, .rsi, .rdi, .r8, .r10, .r11] (sbp_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem simpleBitPack_ct :
    ConstantTime isa simpleBitPackK.pre simpleBitPackK.pub Impl.MlDsa.X86_64.Pack.simpleBitPack :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

/-- In memory of zeros, every coefficient is 0. -/
theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp only [coeffAt, Mem.readW, read_zero]
  rfl

/-- A state satisfying the precondition. -/
def simpleBitPackSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 15 | .rdx => 0x2000 | .rcx => 128 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 128⟩]

theorem simpleBitPack_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Pack.simpleBitPack (simpleBitPackContract X86_64.abi) :=
  Verified.of_correct simpleBitPack_correct simpleBitPack_ct
    { pre := by sig_implies_pre [simpleBitPackContract, simpleBitPackSig, simpleBitPackK, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [simpleBitPackContract, simpleBitPackSig, simpleBitPackK, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [simpleBitPackContract, simpleBitPackSig, simpleBitPackK, X86_64.abi, X86_64.argRegs]
      sat := by
        refine ⟨simpleBitPackSat, ?_⟩
        sig_pre [simpleBitPackContract, simpleBitPackSig, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | exact fun i _ => by rw [coeffAt_zero]; exact Nat.zero_le _
          | (simp only [simpleBitPackBounds, t1Max_eq]; decide)
          | decide }

end VG.Proof.MlDsa.X86_64.Pack
