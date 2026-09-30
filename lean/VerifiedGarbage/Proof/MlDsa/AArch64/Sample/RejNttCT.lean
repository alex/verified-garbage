import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Proof.MlKem.AArch64.Sample

/-!
# ML-DSA on AArch64: `vg_mldsa_rej_ntt_poly`, constant time and verified

Untrusted: everything here is checked by Lean. Two runs whose seeds and
pointers agree leak the same (`RejNtt.ct`), piece by piece (`Rel.lean`),
and the shared contract follows from `rnK` (`rejNTT_verified`).
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G PolyIs coeffAt)
open VG.Spec.Sha3 (bytesAt)

/-- Registers whose values are equal. -/
theorem regs_eq {s₁ s₂ : State} {rs : List Reg} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    ∀ r ∈ rs, s₁.gpr r = s₂.gpr r := h

theorem toNat_inj {a b : BitVec 64} {n : Nat} (ha : a.toNat = n) (hb : b.toNat = n) : a = b :=
  BitVec.eq_of_toNat_eq (ha.trans hb.symm)

/-- The bytes of a polynomial of zeros are zero. -/
theorem byte_zero {m : Mem} {p : Addr} (h : ∀ i < 256, coeffAt m p i = 0) {y : Addr}
    (hy : (polyR p).Contains y 1) : m y = 0 :=
  Proof.MlKem.AArch64.Sample.byte_zero (p := p) (fun i hi => h i hi) hy

namespace RejNtt

/-- The loop's regions. -/
abbrev lrd (σ : State) : List Region := [⟨(spOf σ).at' 840, 1008⟩]
abbrev lwr (σ : State) : List Region := [polyR (σ.gpr .x1)]

theorem pub_msg {σ₁ σ₂ : State} (hq : rnK.pub σ₁ σ₂) : (spOf σ₁).msg σ₁ = (spOf σ₂).msg σ₂ := hq.2.2.2.2

theorem pub_eq {σ₁ σ₂ : State} (hq : rnK.pub σ₁ σ₂) : spOf σ₁ = spOf σ₂ := by
  rw [spOf, spOf, hq.1, hq.2.1, hq.2.2.1]

theorem X_eq {σ₁ σ₂ : State} (hq : rnK.pub σ₁ σ₂) : X σ₁ = X σ₂ := by
  simp only [X, Sp.msg]; rw [hq.2.2.2.2]

theorem loop_ct : RelCT isa (Rel2 rnK.pre rnK.pub Z) rnLoop fun _ _ => True := by
  refine relMem lrd lwr [.x25, .x26]
    (fun σ₁ σ₂ _ _ hq => by simp [lrd, lwr, pub_eq hq, hq.2.1]) (fun σ s hp h => ?_)
    (fun σ s hp h => ?_) (fun σ₁ σ₂ s₁ s₂ p₁ p₂ hq h₁ h₂ => ?_) (by taint_decide)
  · rw [regions (spOk hp) h.env]
    refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
    · rcases mem2 hr with rfl | rfl
      · exact ⟨(spOf σ).scrR, by simp, 840, rfl, by simp⟩
      · exact ⟨polyR (σ.gpr .x1), by simp, 0, (Proof.MlKem.AArch64.ptr_zero _).symm, by simp⟩
    · rw [List.mem_singleton.mp hr, h.env.wr, (spOk hp).wr]
      exact ⟨polyR (σ.gpr .x1), by simp, 0, (Proof.MlKem.AArch64.ptr_zero _).symm, by simp⟩
  · have l := lpre hp h
    obtain ⟨t, u, e, -⟩ := RejNtt.loop_ok (X_length σ) (s₀ := s.withRegions (lrd σ) (lwr σ))
      ⟨l.buf, fun p hp' => Proof.MlKem.AArch64.in_rd (Proof.MlKem.AArch64.in_regions
        (List.mem_singleton_self _) (Offset.contains_base _ (by omega) (by omega))),
        fun i hi => Proof.MlKem.AArch64.in_regions (List.mem_singleton_self _) (coeff_contains _ hi),
        l.disj, l.x25, l.x26⟩
    exact ⟨t, u, e⟩
  · refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.1], fun r hr => ?_, fun x hx => ?_⟩
    · rcases mem2 hr with rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, pub_eq hq]
    · obtain ⟨R, hR, hc⟩ := hx
      rcases mem2 hR with rfl | rfl
      · obtain ⟨p, hp', rfl⟩ := Proof.MlKem.AArch64.Sample.at_off hc
        rw [← MlKem.bytesAt_getD s₁.mem _ hp', h₁.out, pub_eq hq, ← MlKem.bytesAt_getD s₂.mem _ hp', h₂.out, X_eq hq]
      · rw [byte_zero h₁.zero hc, byte_zero h₂.zero (by rw [← hq.2.1]; exact hc)]

theorem regs3 {s₁ s₂ : State} {a b c : Reg} (ha : s₁.gpr a = s₂.gpr a) (hb : s₁.gpr b = s₂.gpr b)
    (hc : s₁.gpr c = s₂.gpr c) : ∀ r ∈ [a, b, c], s₁.gpr r = s₂.gpr r := fun r hr => by
  rcases mem3 hr with rfl | rfl | rfl <;> assumption

theorem ct : ConstantTime isa rnK.pre rnK.pub rejNTT := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono (Q := fun _ _ => True) (P := Rel2 rnK.pre rnK.pub fun σ s => s = σ)
    ?_ (fun s₁ s₂ h => ⟨s₁, s₂, h.1, h.2.1, h.2.2, rfl, rfl⟩) fun _ _ _ => trivial)
  refine RelCT.seq (relTaintStep (J' := fun σ => J0 (spOf σ) σ) [.x0, .x1, .x2]
    (fun σ s hp h => by subst h; exact pro_ok hp) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      subst h₁ h₂; exact ⟨hq.2.2.2.1, regs3 hq.1 hq.2.1 hq.2.2.1⟩) (by taint_decide)) ?_
  refine RelCT.seq (relTaintStep (J' := fun σ => J6 168 1008 (spOf σ) σ) [.x25, .x26, .x27, .x3, .x4]
    (fun σ s hp h => sponge_ok (spOk hp) (by decide) (by decide) h) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.1], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, pub_eq hq]
      · rw [h₁.x3, h₂.x3, pub_eq hq]
      · exact toNat_inj h₁.x4 h₂.x4) (by taint_decide)) ?_
  refine RelCT.seq (relTaintStep (J' := Z) [.x26] (fun σ s hp h => zero_ok hp h)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.1], fun r hr => by
      rw [List.mem_singleton.mp hr, h₁.env.x26, h₂.env.x26, pub_eq hq]⟩) (by taint_decide)) ?_
  refine RelCT.seq (relStep (J' := LP) (fun σ s hp h => loopP_ok hp h) loop_ct) ?_
  exact relTaint [.x25] (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.1],
    fun r hr => by rw [List.mem_singleton.mp hr, h₁.env.x25, h₂.env.x25, pub_eq hq]⟩) (by taint_decide)

end RejNtt

end VG.Proof.MlDsa.AArch64.Sample

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (G)
open VG.Spec.Sha3 (bytesAt)

/-- A state satisfying the precondition. -/
def rnSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem rejNTT_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Sample.rejNTT (Spec.MlDsa.rejNTTContract AArch64.abi 16) :=
  Verified.of_correct RejNtt.correct RejNtt.ct
    { pre := by sig_implies_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, AArch64.abi,
        AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, AArch64.abi, AArch64.argRegs]
        dsimp only [rnK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (rnFold [] (G (bytesAt s.mem (s.gpr .x0) 34) 1008)).length = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with rejNTT := 1008 }, by
            show Spec.MlDsa.rejNTTPoly 1008 _ = _
            rw [rejNTT_some hf, hpoly]⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, rejNTT_none (B := 1008) (by decide) (by decide) hf⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, AArch64.abi, AArch64.argRegs] at h
        obtain ⟨hsp, hb, hx0, hx1, hx2⟩ := h
        exact ⟨hx0, hx1, hx2, hsp, Proof.MlKem.AArch64.Sample.map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, AArch64.abi,
        AArch64.argRegs] [rnSat] using rnSat }

end VG.Proof.MlDsa.AArch64.Sample
