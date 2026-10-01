import VerifiedGarbage.Proof.Rc2.X86.Words
import VerifiedGarbage.Proof.Rc2.Memory

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

structure RoundEnv (s : State) : Prop where
  scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32
  keyFit : (arg s 0).toNat + 128 ≤ 2 ^ 32
  stackRead : InRegions (s.rd ++ s.wr) (argAddr s 0) 4
  keyRead : ∀ i < 128, InRegions (s.rd ++ s.wr) (addr32 (arg s 0) + BitVec.ofNat 64 i) 1
  wordWrite : ∀ i < 4, InRegions s.wr (wordBase s + BitVec.ofNat 64 (4 * i)) 4
  keySep : (Region.mk (addr32 (arg s 0)) 128).Disjoint ⟨wordBase s, 16⟩
  argSep : (Region.mk (argAddr s 0) 4).Disjoint ⟨wordBase s, 16⟩

structure RoundFrame (s₀ s : State) : Prop where
  reg : ∀ r, r ∉ roundWrites → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨wordBase s₀, 16⟩] s₀.mem s.mem

theorem RoundFrame.refl (s : State) : RoundFrame s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem RoundFrame.base {s s' : State} (h : RoundFrame s s') : wordBase s' = wordBase s := by
  unfold wordBase; rw [h.reg .ebp (by decide)]

theorem RoundFrame.argAddr {s s' : State} (h : RoundFrame s s') (i : Nat) : argAddr s' i = argAddr s i := by
  unfold VG.X86.argAddr; rw [h.reg .esp (by decide)]

theorem RoundFrame.arg {s s' : State} (h : RoundFrame s s') (env : RoundEnv s) : arg s' 0 = arg s 0 := by
  unfold VG.X86.arg
  rw [h.argAddr]
  exact h.mem.readW (Region.contains_self _ _) (by simpa using env.argSep) (by decide)

theorem RoundFrame.env {s s' : State} (h : RoundFrame s s') (env : RoundEnv s) : RoundEnv s' := by
  have args := h.arg env
  constructor
  · rw [h.reg .ebp (by decide)]; exact env.scratchFit
  · rw [args]; exact env.keyFit
  · rw [h.rd, h.wr, h.argAddr]; exact env.stackRead
  · rw [h.rd, h.wr, args]; exact env.keyRead
  · rw [h.wr, h.base]; exact env.wordWrite
  · rw [args, h.base]; exact env.keySep
  · rw [h.argAddr, h.base]; exact env.argSep

theorem RoundFrame.schedule {s s' : State} (h : RoundFrame s s') (env : RoundEnv s) :
    Spec.Rc2.scheduleAt s'.mem (addr32 (VG.X86.arg s' 0)) = Spec.Rc2.scheduleAt s.mem (addr32 (VG.X86.arg s 0)) := by
  rw [h.arg env]
  exact scheduleAt_frame h.mem _ (by simpa using env.keySep)

theorem RoundFrame.trans {s₀ s₁ s₂ : State} (h₁ : RoundFrame s₀ s₁) (h₂ : RoundFrame s₁ s₂) :
    RoundFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame := h₂.mem
  rw [h₁.base] at frame
  exact h₁.mem.trans frame

theorem RoundFrame.of_keep {s s' : State} (h : Keep roundWrites s s') : RoundFrame s s' := by
  refine ⟨h.reg, h.rd, h.wr, ?_⟩
  rw [h.mem]; exact Frame.refl _ _

theorem keep_mix_round {s s' : State} {i : Nat} (h : Keep (wordReg i :: temps) s s') :
    Keep roundWrites s s' := h.weaken (by
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with he | ht
  · subst r
    have fact : ∀ j < 4, wordReg j ∈ roundWrites := by decide
    simpa only [wordReg, Nat.mod_mod] using fact (i % 4) (Nat.mod_lt _ (by decide))
  · have sub : ∀ r ∈ temps, r ∈ roundWrites := by decide
    exact sub r ht)

theorem RoundEnv.wordRead {s : State} (h : RoundEnv s) :
    ∀ i < 4, InRegions (s.rd ++ s.wr) (wordBase s + BitVec.ofNat 64 (4 * i)) 4 := by
  intro i hi
  obtain ⟨r, hr, hc⟩ := h.wordWrite i hi
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem storeWord32_ok (s : State) (r : Reg) (i : Nat) (hi : i < 4) (env : RoundEnv s) :
    ∃ s', runBlock isa [.store (memOp .ebp (wordOff i)) r] s = some s' ∧
      s'.mem = s.mem.writeW (wordBase s + BitVec.ofNat 64 (4 * i)) (s.gpr r) ∧
      RoundFrame s s' := by
  have fit := env.scratchFit
  have write : InRegions s.wr (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (wordOff i)) 4 := by
    rw [wordOff_eq s i hi]; exact env.wordWrite i hi
  refine ⟨_, by
    rw [runBlock_cons, exec_store s r .ebp (wordOff i)
      (by simp only [wordOff, Nat.mod_eq_of_lt hi]; omega) write, runStep_some, runBlock_nil], ?_⟩
  constructor
  · rw [wordOff_eq s i hi]
  · refine ⟨fun _ _ => rfl, rfl, rfl, ?_⟩
    rw [wordOff_eq s i hi]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Rc2.X86
