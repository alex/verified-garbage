import VerifiedGarbage.Proof.Rc2.X86.Cbc.Body
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Constant-time CBC steps with public registers restored by the block call -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

def EqKept (s₁ s₂ : State) : Prop := ∀ r ∈ kept, s₁.gpr r = s₂.gpr r

def StepRel (s₁ s₂ : State) : Prop := StepPre s₁ ∧ StepPre s₂ ∧ EqKept s₁ s₂

theorem agreeKept {s₁ s₂ : State} (h : EqKept s₁ s₂) :
    VG.X86.Taint.Agree (τr kept) s₁ s₂ := agree_regs h

theorem before_ok (d : Spec.Rc2.Direction) (s : State) (hp : StepPre s) :
    WP isa (.block (Impl.Rc2.X86.Cbc.before d)) s (fun s' => StepPre s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r) := by
  have sep : ∀ r ∈ kept, r ∉ temps := by decide
  cases d
  · apply WP.mono (xor64_ok s .esi .ecx (by decide) (by decide)
      (by simpa using hp.dataFit) hp.ivFit hp.readData hp.readIv hp.writeData)
    intro s' h
    exact ⟨hp.keep h, fun r hr => h.reg r (sep r hr)⟩
  · apply WP.mono (copy64_ok s .esi .ebp 0 256 (by decide) (by decide)
      (by simpa using hp.dataFit) (by have := hp.bufFit; omega)
      (by simpa using hp.readData) (hp.writeBuf 256 (by decide)))
    intro s' h
    exact ⟨hp.keep h, fun r hr => h.reg r (sep r hr)⟩

theorem kept_ct {c : Prog isa} (h : RelCT isa StepRel c (fun _ _ => True))
    (correct : ∀ s, StepPre s → WP isa c s (fun s' => StepPre s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r)) :
    RelCT isa StepRel c StepRel := by
  apply (h.wpDep (fun s₁ s₂ hp => ⟨correct s₁ hp.1, correct s₂ hp.2.1⟩)).mono
    (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  refine ⟨h₁.1, h₂.1, fun r hr => ?_⟩
  rw [h₁.2 r hr, h₂.2 r hr]
  exact hp.2.2 r hr

theorem before_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (.block (Impl.Rc2.X86.Cbc.before d)) StepRel := by
  apply kept_ct _ (before_ok d)
  cases d <;> apply RelCT.taint (A := taint) (τr kept) (fun _ _ h => agreeKept h.2.2)
  all_goals taint_decide

def callRd (s : State) : List Region :=
  [⟨addr32 (s.gpr .ebx), 128⟩, ⟨argAddr (pushed [.ebp, .esi, .ebx] s).callEntry 0, 12⟩]
def callWr (s : State) : List Region := [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 256⟩]

theorem callPre_ok (d : Spec.Rc2.Direction) (s : State) (hp : CallPre s) :
    VG.X86.CallPre (blockContract d) [.ebp, .esi, .ebx] (callRd s) (callWr s) s := by
  let rs : List Reg := [.ebp, .esi, .ebx]
  have hrs : .esp ∉ rs := by decide
  have fit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := hp.stackLo
  let sE := (pushed rs s).callEntry
  have a0 : arg sE 0 = s.gpr .ebx := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have a1 : arg sE 1 = s.gpr .esi := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have a2 : arg sE 2 = s.gpr .ebp := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have eA : argAddr sE 0 = ((s.gpr .esp) - BitVec.ofNat 32 12).setWidth 64 := by rw [callEntry_argAddr0]; rfl
  have eSp : sE.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 := by rw [callEntry_esp']; rfl
  have b12 : Region.Sub (below (s.gpr .esp) 12) (below (s.gpr .esp) 16) := below_sub (by decide) hp.stackLo
  have r4 : Region.Sub ⟨((s.gpr .esp) - BitVec.ofNat 32 16).setWidth 64, 4⟩ (below (s.gpr .esp) 16) :=
    Region.sub_prefix (by decide)
  unfold callRd callWr
  refine ⟨?_, ?_, ?_⟩
  · change (blockContract d).pre (sE.withRegions _ _)
    simp only [blockContract, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨?_, trivial, hp.keyScratch, hp.dataScratch, hp.stackData.sub_left b12,
      hp.stackBuf.sub_left b12, hp.stackData.sub_left r4, hp.stackBuf.sub_left r4,
      hp.keyFit, hp.dataFit, hp.bufFit, ?_⟩
    · rw [callEntry_argAddr0]; rfl
    rw [sub_toNat hp.stackLo]
    have := (s.gpr .esp).isLt
    omega
  · intro a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · apply InRegions_append_cons.mpr
      left
      rw [eA] at hc
      exact hc
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hp.writes a n h
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩

theorem call_ct (d : Spec.Rc2.Direction) : RelCT isa StepRel (Impl.Rc2.X86.Cbc.blockCall d) StepRel := by
  apply kept_ct
  · intro s₁ s₂ t₁ t₂ u₁ u₂ hp e₁ e₂
    have sp := hp.2.2 .esp (by decide)
    have key := hp.2.2 .ebx (by decide)
    have data := hp.2.2 .esi (by decide)
    have buf := hp.2.2 .ebp (by decide)
    have rd : callRd s₂ = callRd s₁ := by
      simp only [callRd, callEntry_argAddr0, key, sp]
    have wr : callWr s₂ = callWr s₁ := by simp only [callWr, data, buf]
    have hc : ConstantTime isa (blockContract d).pre (blockContract d).pub (.block (blockCode d)) := by
      cases d
      · exact encryptBlock_constantTime
      · exact decryptBlock_constantTime
    have ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (Impl.Rc2.X86.Cbc.blockCall d) (fun _ _ => True) := by
      rw [blockCall_eq]
      apply RelCT.callWith (block_correct d) hc (callRd s₁) (callWr s₁)
      rintro a b ⟨ha, hb⟩
      subst a b
      refine ⟨callPre_ok d s₁ hp.1.call, ?_, sp, ?_⟩
      · rw [← rd, ← wr]; exact callPre_ok d s₂ hp.2.1.call
      · constructor
        · simp only [State.withRegions_gpr, callEntry_esp', sp]
        · intro i hi
          simp only [arg_withRegions]
          rw [callEntry_arg (by exact hp.1.stackLo) (by decide) (by simpa using hi),
            callEntry_arg (by exact hp.2.1.stackLo) (by decide) (by simpa using hi)]
          have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases cases with rfl | rfl | rfl
          · exact key
          · exact data
          · exact buf
    exact ct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  · intro s hp
    apply WP.mono (call_ok d s hp.call)
    intro s' h
    exact ⟨hp.transport h.rd h.wr h.reg, h.reg⟩

theorem after_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (.block (Impl.Rc2.X86.Cbc.after d)) (fun _ _ => True) := by
  cases d <;> apply RelCT.taint (A := taint) (τr kept) (fun _ _ h => agreeKept h.2.2)
  all_goals taint_decide

theorem step_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (Impl.Rc2.X86.Cbc.step d) StepRel := by
  apply kept_ct ((before_ct d).seq ((call_ct d).seq (after_ct d)))
  intro s hp
  apply WP.mono (step_ok d s hp)
  intro s' h
  exact ⟨h.toPinned.pre hp, h.reg⟩

theorem body_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (Impl.Rc2.X86.Cbc.body d) (fun _ _ => True) := by
  apply (step_ct d).seq
  apply RelCT.taint (A := taint) (τr kept) (fun _ _ h => agreeKept h.2.2)
  taint_decide

end VG.Proof.Rc2.X86.Cbc
