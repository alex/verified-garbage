import VerifiedGarbage.Proof.AesGcm.Arm.CTCrypt

/-!
# AES-GCM on ARMv7: `j0` is constant time

Untrusted: everything here is checked by Lean. The invariant fixes the
context, the state, `W`, the stack pointer and the nonce's address and
length.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- Before `j0`. -/
def J0I (c st w sp : BitVec 32) (Np : BitVec 32) (n : Nat) (s : State) : Prop :=
  ∃ k7 k8 H, J0In c st w sp k7 k8 H Np n s

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem j0hash_ct {Np : BitVec 32} {n : Nat} (hlt : n < 2 ^ 32) : CT (J0I c st w sp Np n) j0hash := by
  -- the accumulator zeroed, then the nonce absorbed
  let A : State → Prop := fun s => ∃ k8 H, AbsIn c st w sp (BitVec.ofNat 32 n) k8 0 H [] Np n s ∧
    blockAt s.mem (State.addr st + BitVec.ofNat 64 0) = 0
  refine CT.seq (J := A) ?_ (fun s ⟨k7, k8, H, hs⟩ => WP.mono (j0zero_ok L hs)
    fun s' h => ⟨k8, H, h.1, h.2.1⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5, .r10]) (.block [.mov .r0 (imm 0),
        .str .r0 .r10 0, .str .r0 .r10 4, .str .r0 .r10 8, .str .r0 .r10 12, .mov .r7 (.reg .r5), .mov .r6 (imm 0)])
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r5, h₂.r5]
    · exact h₁.env.pin h₂.env (by simp)
  let E : State → Prop := fun s => ∃ k8, Env c st w sp (BitVec.ofNat 32 n) k8 s
  refine CT.seq (J := E) ((absorb_ct L (.inl rfl) (by decide)).mono fun s ⟨k8, H, hs, _⟩ => ⟨_, k8, H, [], rfl, hs⟩)
    (fun s ⟨k8, H, hs, _⟩ => WP.mono (absorb_ok L (.inl rfl) hs) fun s' h => ⟨k8, h.env⟩) ?_
  -- the length of the nonce modulo 16
  let F : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s ∧ s.gpr .r6 = BitVec.ofNat 32 (n % 16) ∧
    s.gpr .r7 = BitVec.ofNat 32 n
  refine CT.seq (J := F) ?_ (fun s ⟨k8, he⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r7]) (.block [.dp .and .r6 .r7 (imm 15)])
        h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r7, h₂.r7]) hc
  · have hand := and15 (BitVec.ofNat 32 n)
    rw [toNat32 hlt] at hand
    refine WP.of_runBlock ⟨s.setReg .r6 (s.gpr .r7 &&& BitVec.ofNat 32 15), by arun [], _, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, he.r7, hand]
    · simp [gpr_setReg, he.r7]
  let G : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s
  refine CT.seq (J := G) ((flush_ct L (yo := 0) (.inl rfl) (q := n % 16) (Nat.mod_lt _ (by decide))).mono
    fun s ⟨k7, k8, he, h6, _⟩ => ⟨k7, k8, he, h6⟩) (fun s ⟨k7, k8, he, h6, _⟩ => WP.mono
      (flush_ok L (yo := 0) (.inl rfl) (x := List.replicate n 0) (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240))
        ⟨he, rfl⟩ (by rw [h6]; simp)) fun s' h => ⟨k7, k8, h.env⟩) ?_
  refine CT.seq (J := G) ?_ (fun s ⟨k7, k8, he⟩ => ?_) ((lens_ct L (.inl rfl)).mono fun s h => h)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.mov .r4 (imm 0), .mov .r5 (imm 0),
        .mov .r6 (.reg .r7), .mov .r7 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun _ _ _ _ r hr => by simp at hr) hc
  · exact WP.of_runBlock ⟨(((s.setReg .r4 (BitVec.ofNat 32 0)).setReg .r5 (BitVec.ofNat 32 0)).setReg .r6
      (s.gpr .r7)).setReg .r7 (BitVec.ofNat 32 0), by arun [], _, k8, he.set7 (k7' := 0) (by simp [gpr_setReg]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl⟩

theorem j0_ct {Np : BitVec 32} {n : Nat} (hlt : n < 2 ^ 32) : CT (J0I c st w sp Np n) j0 := by
  refine CT.seq (J := fun s => J0I c st w sp Np n s ∧ s.z = decide (n = 12)) ?_ (fun s ⟨k7, k8, H, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 12)])
        h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmpk_ok s .r5 hs.r5 hlt (k := 12) (by decide) (by decide)
    exact WP.of_runBlock ⟨s₁, run₁, ⟨k7, k8, H, ⟨hs.env.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁,
      by rw [hm₁]; exact hs.hH, by rw [hg₁]; exact hs.r4, by rw [hg₁]; exact hs.r5, hs.data.of_eq hrd₁ hwr₁⟩⟩, hz⟩
  let M : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s
  refine CT.seq (J := M) ?_ (fun s ⟨⟨k7, k8, H, hs⟩, hz⟩ => ?_) ?_
  · refine CT.ite (decide (n = 12)) (fun s h => h.2) (fun hb => ?_) (fun _ => (j0hash_ct L hlt).mono fun s h => h.1)
    obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r10]) (.block j012) h).isSome = true :=
      ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, h₁⟩, _⟩ ⟨⟨_, _, _, h₂⟩, _⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · exact h₁.env.pin h₂.env (by simp)
  · refine WP.ite (decide (n = 12)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
    · have h12 : n = 12 := by simpa using ht
      subst h12
      exact WP.mono (j012_ok L hs) fun s' h => h.env.elim fun k7 he => ⟨k7, k8, he⟩
    · exact WP.mono (j0hash_ok L hs (by simpa using hf)) fun s' h => h.env.elim fun k7 he => ⟨k7, k8, he⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r10]) (.block initState) h).isSome = true :=
      ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr => h₁.pin h₂ (by simp at hr; simp [hr])) hc

end

end VG.Proof.AesGcm.Arm
