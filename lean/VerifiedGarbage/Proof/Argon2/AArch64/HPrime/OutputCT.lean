import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Compare
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.FirstCT

/-! # H′: public output counters and prefix emission -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

def LoopReady (s : State) : Prop := OutputReady s ∧ 65 ≤ (s.gpr .x23).toNat

theorem loop_stable : Stable LoopReady where
  ready _ h := output_stable.ready _ h.1
  keeps s t h k := ⟨output_stable.keeps s t h.1 k,
    by rw [k.regs .x23 (by decide) (by decide)]; exact h.2⟩

theorem sub32_nat (v : BitVec 64) (h : 32 ≤ v.toNat) : (v - 32).toNat = v.toNat - 32 := by
  have eq : v - 32 = BitVec.ofNat 64 (v.toNat - 32) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl] using (Offset.ofNat_sub_ofNat (w := 64) h)
  rw [eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.isLt; omega)]

theorem Emitted.ready {s t : State} (h : Emitted s t) (pre : LoopReady s) : OutputReady t := by
  have count : (t.gpr .x23).toNat = (s.gpr .x23).toNat - 32 := by
    rw [h.remaining, sub32_nat _ (by have := pre.2; omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [count]
    apply pre.1.space.advance (Written.of_emitted h)
    simp only [Spec.Blake2.bytesAt, List.length_map, List.length_range]
    have := pre.2
    omega
  · rw [count]; have := pre.2; omega
  · rw [count]; have := pre.1.bound; omega

theorem emit_ready (v : State) (h : LoopReady v) : WP isa emitPrefix v (Emitted v) := by
  have space := h.1.space.prefix (show 32 ≤ (v.gpr .x23).toNat by have := h.2; omega)
  exact emitPrefix_ok v space.work space.out
    (space.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384)))

theorem emit_rel : RelCT isa (Related LoopReady) emitPrefix (Related OutputReady) := by
  have ct := (emitPrefix_rel.mono (P' := Related LoopReady)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨emit_ready s₁ hp.1, emit_ready s₂ hp.2.1⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨pub, _, _, hp, h₁, h₂⟩ =>
    ⟨h₁.ready hp.1, h₂.ready hp.2.1, pub⟩

theorem count64_init_rel {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (.block [.movz .x .x1 64 0])
      (fun s₁ s₂ => Related F s₁ s₂ ∧
        (1 ≤ (s₁.gpr .x1).toNat ∧ (s₁.gpr .x1).toNat ≤ 64) ∧ s₁.gpr .x1 = s₂.gpr .x1) := by
  have ct := (count64_rel stable).wpDep (fun s₁ s₂ _ => ⟨count64_ok s₁, count64_ok s₂⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨⟨hp, eq⟩, _, _, _, ⟨_, len⟩, _⟩ =>
    ⟨hp, by rw [len]; decide, eq⟩

theorem compare_rel (stable : Stable OutputReady) :
    RelCT isa (Related OutputReady) (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63])
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ s₁.gpr .x9 = s₂.gpr .x9 ∧
        s₁.gpr .x9 = if (s₁.gpr .x23).toNat < 65 then 1 else 0) := by
  have ct := (RelCT.taint (A := taint) (P := Related OutputReady) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩)
    (c := .block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63])
    (by taint_decide)).wpDep (fun s₁ s₂ hp => ⟨compare_ok s₁ hp.1.bound, compare_ok s₂ hp.2.1.bound⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, hp, h₁, h₂⟩
  have k₁ := h₁.keeps
  have k₂ := h₂.keeps
  refine ⟨hp.keeps stable k₁ k₂, ?_, ?_⟩
  · rw [h₁.value, h₂.value, hp.2.2.2 .x23 (by decide)]
  · rw [k₁.regs .x23 (by decide) (by decide)]; exact h₁.value

end VG.Proof.Argon2.AArch64.HPrime
