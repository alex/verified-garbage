import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.FirstCT

/-! # H′: public output counters and prefix emission -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_cmpi)

def LoopReady (s : State) : Prop := OutputReady s ∧ 65 ≤ (s.gpr .r15).toNat

theorem loop_stable : Stable LoopReady where
  ready _ h := output_stable.ready _ h.1
  keeps s t h k := ⟨output_stable.keeps s t h.1 k,
    by rw [k.regs .r15 (by decide)]; exact h.2⟩

theorem sub32_nat (v : BitVec 64) (h : 32 ≤ v.toNat) : (v - 32).toNat = v.toNat - 32 := by
  have eq : v - 32 = BitVec.ofNat 64 (v.toNat - 32) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl] using (Offset.ofNat_sub_ofNat (w := 64) h)
  rw [eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.isLt; omega)]

theorem Emitted.ready {s t : State} (h : Emitted s t) (pre : LoopReady s) : OutputReady t := by
  have count : (t.gpr .r15).toNat = (s.gpr .r15).toNat - 32 := by
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
  have space := h.1.space.prefix (show 32 ≤ (v.gpr .r15).toNat by have := h.2; omega)
  exact emitPrefix_ok v space.work space.out
    (space.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384)))

theorem emit_rel : RelCT isa (Related LoopReady) emitPrefix (Related OutputReady) := by
  have ct := (emitPrefix_rel.mono (P' := Related LoopReady)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨emit_ready s₁ hp.1, emit_ready s₂ hp.2.1⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨pub, _, _, hp, h₁, h₂⟩ =>
    ⟨h₁.ready hp.1, h₂.ready hp.2.1, pub⟩

theorem count64_init_rel {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (.block [.mov32 .rsi (.imm 64)])
      (fun s₁ s₂ => Related F s₁ s₂ ∧
        (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  have ct := (count64_rel stable).wpDep (fun s₁ s₂ _ => ⟨count64_ok s₁, count64_ok s₂⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨⟨hp, eq⟩, _, _, _, ⟨_, len⟩, _⟩ =>
    ⟨hp, by rw [len]; decide, eq⟩

theorem compare_ok (s : State) : WP isa (.block [.alu .cmp .r15 (.imm 65)]) s fun t =>
    Keeps s t ∧ t.cf = some (decide ((s.gpr .r15).toNat < 65)) := by
  refine wp_cmpi fun t gt mt rt wt cf _ => WP.block_nil ⟨?_, cf⟩
  exact ⟨fun r _ => congrFun gt r, rt, wt, by rw [mt]; exact Frame.refl _ _⟩

theorem compare_rel {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (.block [.alu .cmp .r15 (.imm 65)])
      (fun s₁ s₂ => Related F s₁ s₂ ∧ s₁.cf = s₂.cf ∧
        s₁.cf = some (decide ((s₁.gpr .r15).toNat < 65))) := by
  have ct := (RelCT.taint (A := taint) (P := Related F) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block [.alu .cmp .r15 (.imm 65)])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨compare_ok s₁, compare_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, hp, ⟨k₁, cf₁⟩, ⟨k₂, cf₂⟩⟩
  refine ⟨hp.keeps stable k₁ k₂, ?_, ?_⟩
  · rw [cf₁, cf₂, hp.2.2 .r15 (by decide)]
  · rw [k₁.regs .r15 (by decide)]; exact cf₁

end VG.Proof.Argon2.X86_64.HPrime
