import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Correct
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Contract
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Setup
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Compare
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Length
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Input
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Space
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.FixedCT

/-! Merged from `Proof.Argon2.AArch64.HPrime.OutputCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.HPrime.NextCT`. -/
section
/-! # H′: constant time of hashing the previous digest -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_movz)

theorem count64_ok (s : State) : WP isa (.block [.movz .x .x1 64 0]) s fun t =>
    Keeps s t ∧ t.gpr .x1 = 64 := by
  refine wp_movz fun t ht => WP.block_nil ⟨?_, ht.gpr⟩
  refine ⟨fun r hr _ => ?_, ht.rd, ht.wr, ht.sp, ?_⟩
  · have hn : r ≠ .x1 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ht.other r hn
  · rw [ht.mem]; exact Frame.refl _ _

theorem count64_rel {F : State → Prop} (stable : Stable F) :
    RelCT isa (Related F) (.block [.movz .x .x1 64 0])
      (fun s₁ s₂ => Related F s₁ s₂ ∧ s₁.gpr .x1 = s₂.gpr .x1) := by
  have ct := (RelCT.taint (A := taint) (P := Related F) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩) (c := .block [.movz .x .x1 64 0])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨count64_ok s₁, count64_ok s₂⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, k₁, k₂⟩ =>
    ⟨hp.keeps stable k₁.1 k₂.1, k₁.2.trans k₂.2.symm⟩

theorem next_rel (v : Backend) {F : State → Prop} (stable : Stable F) :
    RelCT isa (fun s₁ s₂ => Related F s₁ s₂ ∧
      (1 ≤ (s₁.gpr .x1).toNat ∧ (s₁.gpr .x1).toNat ≤ 64) ∧ s₁.gpr .x1 = s₂.gpr .x1)
      (next v.hash) (Related F) :=
  (stable_init_rel v stable).seq
    ((absorbFixed_rel v 768 64 (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩ stable).seq
      ((count64_rel stable).seq (stable_finalize_rel v stable)))

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.InputCT`. -/
section
/-! # H′: public input bounds and constant-time absorption -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure OutputReady (s : State) : Prop where
  space : Space s (s.gpr .x23).toNat
  positive : 1 ≤ (s.gpr .x23).toNat
  bound : (s.gpr .x23).toNat < 2 ^ 32

theorem output_stable : Stable OutputReady where
  ready _ h := ⟨h.space.spBound, h.space.work, h.space.stackWork⟩
  keeps s t h k := by
    have n := k.regs .x23 (by decide) (by decide)
    refine ⟨?_, ?_, ?_⟩
    · rw [n]; exact h.space.keeps k
    · rw [n]; exact h.positive
    · rw [n]; exact h.bound

structure FirstReady (s : State) : Prop extends OutputReady s where
  length : (s.gpr .x21).toNat < 2 ^ 32
  data : Covers [⟨s.gpr .x20, (s.gpr .x21).toNat⟩] (s.rd ++ s.wr)
  dataWork : (⟨s.gpr .x20, (s.gpr .x21).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩
  stackData : (below s.sp 16).Disjoint ⟨s.gpr .x20, (s.gpr .x21).toNat⟩

theorem first_stable : Stable FirstReady where
  ready _ h := output_stable.ready _ h.toOutputReady
  keeps s t h k := by
    have ptr := k.regs .x20 (by decide) (by decide)
    have len := k.regs .x21 (by decide) (by decide)
    refine ⟨output_stable.keeps s t h.toOutputReady k, ?_, ?_, ?_, ?_⟩
    · rw [len]; exact h.length
    · rw [ptr, len, k.rd, k.wr]; exact h.data
    · rw [ptr, len, k.x24]; exact h.dataWork
    · rw [ptr, len, k.sp]; exact h.stackData

theorem input_ready {s t : State} (ready : FirstReady s) (h : InputArgs s t) : UpdateReady t := by
  have k := h.keeps
  refine ⟨(first_stable.ready _ (first_stable.keeps _ _ ready k)).spBound,
    (first_stable.ready _ (first_stable.keeps _ _ ready k)).work, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.data, h.size, h.rd, h.wr]; exact ready.data
  · rw [h.data, h.size, k.x24]; exact ready.dataWork.sub_right (Region.sub_prefix (by decide))
  · rw [h.data, h.size, k.x24]; exact ready.dataWork.sub_right (Offset.sub_base _ (by decide))
  · rw [k.x24, k.sp]; exact ready.space.stackWork
  · rw [h.data, h.size, k.sp]; exact ready.stackData

theorem absorbInput_keeps (v : Backend) (s : State) (h : FirstReady s) :
    WP isa (absorbInput v.hash) s (Keeps s) := by
  unfold absorbInput
  refine WP.seq ((inputArgs_ok s).mono fun u hu => ?_)
  exact (update_keeps v u (input_ready h hu)).mono fun _ ht => hu.keeps.trans ht

theorem absorbInput_rel (v : Backend) :
    RelCT isa (Related FirstReady) (absorbInput v.hash) (Related FirstReady) := by
  have args := (RelCT.taint (A := taint) (P := Related FirstReady) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩) (c := .block inputArgs) (by taint_decide)).wpDep
    (F := InputArgs) fun s₁ s₂ _ => ⟨inputArgs_ok s₁, inputArgs_ok s₂⟩
  have call := update_rel v (P := fun s₁ s₂ => True ∧
      ∃ σ₁ σ₂, Related FirstReady σ₁ σ₂ ∧ InputArgs σ₁ s₁ ∧ InputArgs σ₂ s₂)
    fun _ _ ⟨_, _, _, hp, h₁, h₂⟩ => by
      exact ⟨input_ready hp.1 h₁, input_ready hp.2.1 h₂,
        by rw [h₁.keeps.x24, h₂.keeps.x24]; exact hp.2.2.2 _ (by decide),
        by rw [h₁.count, h₂.count],
        by rw [h₁.data, h₂.data]; exact hp.2.2.2 _ (by decide),
        by rw [h₁.size, h₂.size]; exact hp.2.2.2 _ (by decide),
        by rw [h₁.keeps.sp, h₂.keeps.sp]; exact hp.2.2.1⟩
  exact keeps_rel first_stable (args.seq call)
    (fun s₁ s₂ hp => ⟨absorbInput_keeps v s₁ hp.1, absorbInput_keeps v s₂ hp.2.1⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.FirstCT`. -/
section
/-! # H′: constant time of the initial length-prefixed hash -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov wp_addImm)

theorem chooseFirst_rel : RelCT isa (Related FirstReady) chooseLength
    (fun s₁ s₂ => Related FirstReady s₁ s₂ ∧
      (1 ≤ (s₁.gpr .x1).toNat ∧ (s₁.gpr .x1).toNat ≤ 64) ∧ s₁.gpr .x1 = s₂.gpr .x1) := by
  have ct := (chooseLength_rel.mono (P' := Related FirstReady)
    (fun _ _ hp => hp.2.2) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨chooseLength_ok s₁ hp.1.bound, chooseLength_ok s₂ hp.2.1.bound⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨pub, s₁, s₂, hp, ⟨len₁, k₁⟩, ⟨_, k₂⟩⟩
  refine ⟨hp.keeps first_stable k₁ k₂, ?_, pub.2 _ (List.mem_cons_self ..)⟩
  rw [len₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : min (s₁.gpr .x23).toNat 64 < 2 ^ 64)]
  have := hp.1.positive
  omega

theorem inputCount_ok (s : State) :
    WP isa (.block [.addImm .x .x1 .x21 0, .addImm .x .x1 .x1 4]) s fun t =>
      Keeps s t ∧ t.gpr .x1 = s.gpr .x21 + 4 := by
  refine wp_mov fun a ha => wp_addImm (by decide) fun t ht => WP.block_nil ⟨?_, ?_⟩
  · refine ⟨fun r hr _ => ?_, ht.rd.trans ha.rd, ht.wr.trans ha.wr, ht.sp.trans ha.sp, ?_⟩
    · have hn : r ≠ .x1 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (ht.other r hn).trans (ha.other r hn)
    · rw [ht.mem, ha.mem]; exact Frame.refl _ _
  · rw [ht.gpr, ha.gpr]; rfl

theorem inputCount_rel :
    RelCT isa (Related FirstReady) (.block [.addImm .x .x1 .x21 0, .addImm .x .x1 .x1 4])
      (fun s₁ s₂ => Related FirstReady s₁ s₂ ∧ s₁.gpr .x1 = s₂.gpr .x1) := by
  have ct := (RelCT.taint (A := taint) (P := Related FirstReady) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩)
    (c := .block [.addImm .x .x1 .x21 0, .addImm .x .x1 .x1 4]) (by taint_decide)).wpDep
    (fun s₁ s₂ _ => ⟨inputCount_ok s₁, inputCount_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, hp, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩
  refine ⟨hp.keeps first_stable k₁ k₂, ?_⟩
  rw [c₁, c₂, hp.2.2.2 .x21 (by decide)]

theorem first_rel (v : Backend) :
    RelCT isa (Related FirstReady) (first v.hash) (Related FirstReady) :=
  chooseFirst_rel.seq ((stable_init_rel v first_stable).seq
    ((absorbFixed_rel v 832 4 (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩ first_stable).seq
    ((absorbInput_rel v).seq (inputCount_rel.seq (stable_finalize_rel v first_stable)))))

end VG.Proof.Argon2.AArch64.HPrime
end

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
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.FinishCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.HPrime.ChainCT`. -/
section
/-! # H′: constant time of the long-output loop -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem chainBody_rel (v : Backend) :
    RelCT isa (Related LoopReady)
      (.seq (.block [.movz .x .x1 64 0])
        (.seq (next v.hash) (.seq emitPrefix (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63]))))
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ s₁.gpr .x9 = s₂.gpr .x9 ∧
        s₁.gpr .x9 = if (s₁.gpr .x23).toNat < 65 then 1 else 0) :=
  (count64_init_rel loop_stable).seq ((next_rel v loop_stable).seq
    (emit_rel.seq (compare_rel output_stable)))

theorem chainStep_ready (v : Backend) (s : State) (h : LoopReady s) :
    WP isa (.seq (.block [.movz .x .x1 64 0])
      (.seq (next v.hash) (.seq emitPrefix (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63])))) s (ChainStep s) := by
  have space := h.1.space.prefix (show 32 ≤ (s.gpr .x23).toNat by have := h.2; omega)
  exact chainStep_ok v s space.spBound ⟨by have := h.2; omega, h.1.bound⟩ space.work space.out space.sep space.stackWork

theorem chain_rel (v : Backend) :
    RelCT isa (Related LoopReady) (chain v.hash)
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64) := by
  let I := fun n s₁ s₂ => Related LoopReady s₁ s₂ ∧ (s₁.gpr .x23).toNat = n
  have step (n : Nat) := ((chainBody_rel v).mono (P' := I n)
    (fun _ _ h => h.1) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨chainStep_ready v s₁ hp.1.1, chainStep_ready v s₂ hp.1.2.1⟩)
  have loops (n : Nat) : RelCT isa (I n) (chain v.hash)
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64) := by
    unfold chain
    apply RelCT.loop (M := isa) I ?_ n
    intro m
    apply (step m).mono (fun _ _ h => h)
    rintro t₁ t₂ ⟨⟨ready, cf, value⟩, s₁, s₂, hp, h₁, _⟩
    refine ⟨by simp only [eval, State.read, cf], ?_, ?_⟩
    · intro flag
      refine ⟨ready, ?_⟩
      by_contra h
      have hn : ¬ (t₁.gpr .x23).toNat < 65 := by omega
      simp [eval, State.read, value, hn] at flag
    intro flag
    have lo : 65 ≤ (t₁.gpr .x23).toNat := by
      by_contra h
      have lt : (t₁.gpr .x23).toNat < 65 := by omega
      simp [eval, State.read, value, lt] at flag
    have remain : (t₁.gpr .x23).toNat = (s₁.gpr .x23).toNat - 32 := by
      rw [h₁.remaining, sub32_nat _ (by have := hp.1.1.2; omega)]
    refine ⟨(t₁.gpr .x23).toNat, ?_, ⟨⟨ready.1, lo⟩, ⟨ready.2.1, ?_⟩, ready.2.2⟩, rfl⟩
    · have before : 65 ≤ (s₁.gpr .x23).toNat := hp.1.1.2
      have count : (s₁.gpr .x23).toNat = m := hp.2
      omega
    · rw [← ready.2.2.2 .x23 (by decide)]; exact lo
  exact (RelCT.exists_ loops).mono (fun s₁ _ h => ⟨(s₁.gpr .x23).toNat, h, rfl⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: constant time of the final hash and output -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov)

def OutputCompared (s t : State) : Prop := Related OutputReady s t ∧ s.gpr .x9 = t.gpr .x9 ∧
  s.gpr .x9 = if (s.gpr .x23).toNat < 65 then 1 else 0

theorem OutputCompared.short {s t : State} (h : OutputCompared s t) (flag : isa.eval (.nonzero .x .x9) s = some true) :
    (s.gpr .x23).toNat ≤ 64 := by
  by_contra hn
  have n : ¬ (s.gpr .x23).toNat < 65 := by omega
  simp [eval, State.read, h.2.2, n] at flag

theorem OutputCompared.long {s t : State} (h : OutputCompared s t) (flag : isa.eval (.nonzero .x .x9) s = some false) :
    Related LoopReady s t := by
  have n : 65 ≤ (s.gpr .x23).toNat := by
    by_contra hn
    have n : (s.gpr .x23).toNat < 65 := by omega
    simp [eval, State.read, h.2.2, n] at flag
  exact ⟨⟨h.1.1, n⟩, ⟨h.1.2.1, by rw [← h.1.2.2.2 .x23 (by decide)]; exact n⟩, h.1.2.2⟩

theorem maybeChain_rel (v : Backend) :
    RelCT isa OutputCompared (.ite (.nonzero .x .x9) (.block []) (chain v.hash))
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64) :=
  RelCT.ite (fun _ _ h => by simp only [eval, State.read, h.2.1])
    (RelCT.block_nil fun _ _ ⟨h, flag⟩ => ⟨h.1, h.short flag⟩)
    ((chain_rel v).mono (fun _ _ ⟨h, flag⟩ => h.long flag) (fun _ _ h => h))

theorem lastCount_ok (s : State) : WP isa (.block [.addImm .x .x1 .x23 0]) s fun t =>
    Keeps s t ∧ t.gpr .x1 = s.gpr .x23 := by
  refine wp_mov fun t ht => WP.block_nil ⟨?_, ht.gpr⟩
  exact Keeps.of_upd ht (by decide)

theorem lastCount_rel :
    RelCT isa (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64)
      (.block [.addImm .x .x1 .x23 0])
      (fun s₁ s₂ => Related OutputReady s₁ s₂ ∧
        (1 ≤ (s₁.gpr .x1).toNat ∧ (s₁.gpr .x1).toNat ≤ 64) ∧ s₁.gpr .x1 = s₂.gpr .x1) := by
  let P := fun s₁ s₂ => Related OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64
  have ct := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.1.2.2.1, by simp [Taint.ofRegs]⟩) (c := .block [.addImm .x .x1 .x23 0])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨lastCount_ok s₁, lastCount_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, ⟨hp, bound⟩, ⟨k₁, n₁⟩, ⟨k₂, n₂⟩⟩
  exact ⟨hp.keeps output_stable k₁ k₂, by rw [n₁]; exact ⟨hp.1.positive, bound⟩,
    by rw [n₁, n₂]; exact hp.2.2.2 _ (by decide)⟩

theorem extendDigest_rel (v : Backend) :
    RelCT isa (Related LoopReady) (extendDigest v.hash) (Related OutputReady) :=
  emit_rel.seq ((compare_rel output_stable).seq
    ((maybeChain_rel v).seq (lastCount_rel.seq (next_rel v output_stable))))

theorem finishOutput_rel (v : Backend) :
    RelCT isa (Related OutputReady) (finishOutput v.hash) (AgreeRegs publicRegs) := by
  have branches : RelCT isa OutputCompared (.ite (.nonzero .x .x9) (.block []) (extendDigest v.hash)) (Related OutputReady) :=
    RelCT.ite (fun _ _ h => by simp only [eval, State.read, h.2.1])
      (RelCT.block_nil fun _ _ h => h.1.1)
      ((extendDigest_rel v).mono (fun _ _ ⟨h, flag⟩ => h.long flag) (fun _ _ h => h))
  exact (compare_rel output_stable).seq (branches.seq
    (copyRemaining_rel.mono (fun _ _ h => h.2.2) (fun _ _ h => h)))

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.CT`. -/
section
/-! # H′: constant time of the complete ARM64 program -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem setup_work (s : State) (h : localContract.pre s) :
    (⟨s.gpr .x4, 16384⟩ : Region) ∈ s.wr := by
  rw [h.2.1]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem setup_ready {s t : State} (h : localContract.pre s) (ht : Setup s t) : FirstReady t := by
  obtain ⟨rd, wr, len, lo, hi, hsp, dw, ow, sd, so, sw⟩ := h
  have sp := ht.sp
  have space : Space t (s.gpr .x3).toNat := by
    refine ⟨hi, by rw [sp]; exact hsp, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ht.workspace, ht.wr, wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · intro i hi'
      rw [ht.wr, ht.output, wr]
      exact ⟨outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
    · rw [ht.workspace, ht.output]; exact ow.symm
    · rw [sp, ht.workspace]; exact sw
    · rw [sp, ht.output]; exact so
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [ht.remaining]; exact space
  · rw [ht.remaining]; exact lo
  · rw [ht.remaining]; exact hi
  · rw [ht.length]; exact len
  · rw [ht.input, ht.length, ht.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · rw [ht.input, ht.length, ht.workspace]; exact dw
  · rw [sp, ht.input, ht.length]; exact sd

theorem code_ct (v : Backend) :
    ConstantTime isa localContract.pre localContract.pub (code v.hash) := by
  let P := fun s₁ s₂ => localContract.pre s₁ ∧ localContract.pre s₂ ∧ localContract.pub s₁ s₂
  have setupCT := (setup_rel.mono (P' := P) (fun s₁ s₂ hp => by
      obtain ⟨di, si, dx, cx, r8, sp⟩ := hp.2.2
      refine ⟨sp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨setup_ok s₁ (setup_work s₁ hp.1), setup_ok s₂ (setup_work s₂ hp.2.1)⟩)
  have start : RelCT isa P (.block setup) (Related FirstReady) :=
    setupCT.mono (fun _ _ h => h) fun _ _ ⟨pub, _, _, hp, h₁, h₂⟩ =>
      ⟨setup_ready hp.1 h₁, setup_ready hp.2.1 h₂, pub⟩
  have firstCT := (first_rel v).mono (fun _ _ h => h)
    (fun _ _ h => (show Related OutputReady _ _ from ⟨h.1.toOutputReady, h.2.1.toOutputReady, h.2.2⟩))
  have restoreCT := restore_rel.mono (P' := AgreeRegs publicRegs) (fun _ _ hp => by
      refine ⟨hp.1, fun r hr => ?_⟩
      simp only [List.mem_singleton] at hr; subst r
      exact hp.2 _ (by decide)) (fun _ _ h => h)
  exact (start.seq (firstCT.seq ((finishOutput_rel v).seq restoreCT))).constantTime

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # Verified ARM64 H′ for every supplied BLAKE2b backend -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem verified (v : Backend) :
    Verified AArch64.target (code v.hash) (Spec.Argon2.hPrimeContract AArch64.abi 16) :=
  Verified.of_correct (code_correct v) (code_ct v) contract_implies

theorem spSafe (v : Backend) : (code v.hash).all (fun i => !isa.writesSp i) = true := by
  induction code v.hash <;> simp_all [Code.all]

end VG.Proof.Argon2.AArch64.HPrime
