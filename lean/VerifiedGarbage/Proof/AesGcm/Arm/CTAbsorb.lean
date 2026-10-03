import VerifiedGarbage.Proof.AesGcm.Arm.CTBase

/-!
# AES-GCM on ARMv7: `ghash1`, `absorb`, `flush` and `lens` are constant time

Untrusted: everything here is checked by Lean. The invariants fix the
context, the state, `W`, the stack pointer, the data's address and length and
the number of bytes absorbed so far modulo 16, and leave the rest
existential.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

theorem Env.pin {c st w sp a b a' b' : BitVec 32} {s₁ s₂ : State} (h₁ : Env c st w sp a b s₁)
    (h₂ : Env c st w sp a' b' s₂) {r : Reg} (hr : r = .r9 ∨ r = .r10 ∨ r = .r11) : s₁.gpr r = s₂.gpr r := by
  rcases hr with rfl | rfl | rfl
  · rw [h₁.r9, h₂.r9]
  · rw [h₁.r10, h₂.r10]
  · rw [h₁.r11, h₂.r11]

/-- Before `ghash1 yo b o`, for the block at `P`. -/
structure GhIn (c st w sp : BitVec 32) (b : Reg) (o : Nat) (P : BitVec 32) (s : State) : Prop where
  env : ∃ k7 k8, Env c st w sp k7 k8 s
  hP : s.gpr b + BitVec.ofNat 32 o = P
  hpr : Covers [⟨State.addr P, 16⟩] (s.rd ++ s.wr)

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem ghash1_ct {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {b : Reg} {o : Nat}
    (hbo : (b = .r10 ∧ o = 32) ∨ (b = .r11 ∧ o = 96)) {P : BitVec 32} (hfit : P.toNat + 16 ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16⟩)
    (hpw : (⟨State.addr P, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below sp).Disjoint ⟨State.addr P, 16⟩) :
    CT (GhIn c st w sp b o P) (ghash1 yo b o) := by
  have hb : b = .r10 ∨ b = .r11 := by rcases hbo with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have he : encodable (BitVec.ofNat 32 o) = true := by rcases hbo with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hey : encodable (BitVec.ofNat 32 yo) = true := by rcases hyo with rfl | rfl <;> decide
  let J : State → Prop := fun s => GhCall s (c + BitVec.ofNat 32 240) (st + BitVec.ofNat 32 yo) P
    (w + BitVec.ofNat 32 512) 1 ∧ s.sp = sp
  refine CT.seq (J := J) ?_ (fun s ⟨⟨k7, k8, hs⟩, hP, hpr⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r9, .r10, .r11])
        (.block [addI .r0 .r9 240, addI .r1 .r10 yo, addI .r2 b o, .mov .r3 (imm 1), addI .r12 .r11 scrO]) h).isSome =
        true := by
      rcases hyo with rfl | rfl <;> rcases hbo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, by taint_decide⟩
    exact CT.taint [.r9, .r10, .r11] (fun s₁ s₂ ⟨⟨_, _, h₁⟩, _, _⟩ ⟨⟨_, _, h₂⟩, _, _⟩ r hr => h₁.pin h₂ (by simpa using hr))
      hc
  · obtain ⟨s₁, run₁, h0, h1, h2, h3, h12, hkeep, hk⟩ := ghArgs_ok hs yo b o hb hey he
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have he₁ : Env c st w sp k7 k8 s₁ := hs.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hkeep _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) hk.sp hk.rd hk.wr
    exact ⟨ghCall_mk L hyo he₁ h0 h1 (by rw [h2, hP]) h3 h12 (by omega) (by simpa using hpy) (by simpa using hpw)
      (by simpa using hpk) (by rw [hk.rd, hk.wr]; simpa using hpr), he₁.sp⟩
  · exact CT.gh fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, h₁.1, h₂.1, h₁.2.trans h₂.2.symm⟩

end

/-- Before `absorb yo`: `q` bytes in the buffer. -/
def AbsI (c st w sp : BitVec 32) (yo : Nat) (D : BitVec 32) (n q : Nat) (s : State) : Prop :=
  ∃ k7 k8 H x, x.length % 16 = q ∧ AbsIn c st w sp k7 k8 yo H x D n s

/-- Part of the way, `j` bytes absorbed. -/
def MidI (c st w sp : BitVec 32) (yo : Nat) (D : BitVec 32) (n q j : Nat) (s : State) : Prop :=
  ∃ k7 k8 H x m₀, x.length % 16 = q ∧ AbsMid c st w sp k7 k8 yo H x D n m₀ j s

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem absorbHead_ct {D : BitVec 32} {n q : Nat} (hn : n ≠ 0) (hq : q ≠ 0) :
    CT (AbsI c st w sp yo D n q) (absorbHead yo) := by
  let J : State → Prop := fun s => ∃ k7 k8 H x m₀ k, x.length % 16 = q ∧ HeadMid c st w sp k7 k8 yo H x D n m₀ k s
  refine CT.seq (J := J) ?_ (fun s ⟨k7, k8, H, x, hx, hs⟩ => WP.mono (headPre_ok L hyo hs hn (by omega))
    fun s' ⟨k, hm⟩ => ⟨k7, k8, H, x, s.mem, k, hx, hm⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r10]) headPre h).isSome =
        true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, x₁, hx₁, h₁⟩ ⟨_, _, _, x₂, hx₂, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
    · rw [h₁.r6, h₂.r6, hx₁, hx₂]
    · exact h₁.env.pin h₂.env (by simp)
  · refine CT.ite (decide (q + min (16 - q) n = 16)) (fun s ⟨_, _, _, _, _, _, hx, hm⟩ => by
      rw [hm.z, hm.kmin, hx]) (fun _ => ?_) (fun _ => CT.skip)
    have eB := L.stA (d := 32) (by decide)
    have hf : (st + BitVec.ofNat 32 32).toNat + 16 ≤ 2 ^ 32 := by rw [L.stN (by decide)]; have := L.sw; omega
    refine (ghash1_ct L hyo (.inl ⟨rfl, rfl⟩) (P := st + BitVec.ofNat 32 32) hf ?_ ?_ ?_).mono
      fun s ⟨k7, k8, _, _, _, _, _, hm⟩ => ⟨⟨k7, k8, hm.env⟩, by rw [hm.env.r10], ?_⟩
    · rw [eB]; exact Lay.st_st (.inl (by omega)) (by omega) (by decide)
    · rw [eB]; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · rw [eB]; exact L.stk_st (by decide)
    · rw [eB]; exact covers_left (hm.env.perm.stC (by decide))

theorem absorbFill_ct {D : BitVec 32} {n q : Nat} (hn : n ≠ 0) (hq : q < 16) :
    CT (AbsI c st w sp yo D n q) (absorbFill yo) := by
  refine CT.seq (J := fun s => AbsI c st w sp yo D n q s ∧ s.z = decide (q = 0)) ?_
    (fun s ⟨k7, k8, H, x, hx, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6]) (.block [.cmp .r6 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, x₁, hx₁, h₁⟩ ⟨_, _, _, x₂, hx₂, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r6, h₂.r6, hx₁, hx₂]) hc
  · obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂, hsp₂⟩ := cmp0_ok s .r6 hs.r6 (by omega)
    exact WP.of_runBlock ⟨s₂, run₂, ⟨k7, k8, H, x, hx, hs.keep hg₂ ⟨hm₂, hrd₂, hwr₂, hsp₂⟩⟩, by rw [hz₂, hx]⟩
  · exact CT.ite (decide (q = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hb =>
      (absorbHead_ct L hyo hn (by simpa using hb)).mono fun s h => h.1

theorem absorbWhole_ct {D : BitVec 32} {n q j : Nat} : CT (MidI c st w sp yo D n q j) (absorbWhole yo) := by
  let nb := (n - j) / 16
  let J₁ : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s ∧ DataOk st w sp s D n ∧ j ≤ n ∧
    s.gpr .r2 = D + BitVec.ofNat 32 j ∧ s.gpr .r3 = BitVec.ofNat 32 nb ∧ s.z = decide (nb = 0)
  refine CT.seq (J := J₁) ?_ (fun s ⟨k7, k8, H, x, m₀, hx, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5]) (.block splitWhole) h).isSome =
        true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
  · obtain ⟨s₁, run₁, h2, h3, -, -, hz, hg₁, hk₁⟩ := split_ok hs.le hs.data.lt32 hs.r4 hs.r5
    refine WP.of_runBlock ⟨s₁, run₁, k7, k8, hs.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr, hs.le, h2, h3, hz⟩
  · refine CT.ite (decide (nb = 0)) (fun s h => by obtain ⟨_, _, _, _, _, _, _, hz⟩ := h; exact hz)
      (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    let J₂ : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s ∧ DataOk st w sp s D n ∧ j ≤ n ∧
      s.gpr .r0 = c + BitVec.ofNat 32 240 ∧ s.gpr .r1 = st + BitVec.ofNat 32 yo ∧
      s.gpr .r2 = D + BitVec.ofNat 32 j ∧ s.gpr .r3 = BitVec.ofNat 32 nb ∧ s.gpr .r12 = w + BitVec.ofNat 32 512
    refine CT.seq (J := J₂) ?_ (fun s ⟨k7, k8, he, hd, hj, h2, h3, _⟩ => ?_) ?_
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r9, .r10, .r11])
          (.block [addI .r0 .r9 240, addI .r1 .r10 yo, addI .r12 .r11 scrO]) h).isSome = true := by
        rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
      exact CT.taint _ (fun s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => h₁.pin h₂ (by simpa using hr)) hc
    · have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
      have ey : encodable (BitVec.ofNat 32 yo) = true := by rcases hyo with rfl | rfl <;> decide
      refine WP.of_runBlock ⟨((s.setReg .r0 (s.gpr .r9 + BitVec.ofNat 32 240)).setReg .r1
        (s.gpr .r10 + BitVec.ofNat 32 yo)).setReg .r12 (s.gpr .r11 + BitVec.ofNat 32 512), by arun [ey], k7, k8, he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hd.of_eq rfl rfl, hj, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h9]
      · simp [gpr_setReg, h10]
      · simp [gpr_setReg, h2]
      · simp [gpr_setReg, h3]
      · simp [gpr_setReg, h11]
    · refine CT.gh fun s₁ s₂ ⟨_, _, he₁, hd₁, hj₁, a0, a1, a2, a3, a12⟩ ⟨_, _, he₂, hd₂, hj₂, b0, b1, b2, b3, b12⟩ => ?_
      have hdj₁ := hd₁.sub (j := j) (k := 16 * nb) (by omega) (by omega)
      have hdj₂ := hd₂.sub (j := j) (k := 16 * nb) (by omega) (by omega)
      exact ⟨_, _, _, _, _, ghCall_mk L hyo he₁ a0 a1 a2 a3 a12 (by have := hdj₁.fit; omega)
        (hdj₁.st.sub_right (Lay.stSub (by omega))).symm (hdj₁.w.sub_right (Lay.wSub (by decide))) hdj₁.stk hdj₁.rd,
        ghCall_mk L hyo he₂ b0 b1 b2 b3 b12 (by have := hdj₂.fit; omega)
        (hdj₂.st.sub_right (Lay.stSub (by omega))).symm (hdj₂.w.sub_right (Lay.wSub (by decide))) hdj₂.stk hdj₂.rd,
        he₁.sp.trans he₂.sp.symm⟩

omit L hyo in
theorem absorbTail_ct {D : BitVec 32} {n q j : Nat} : CT (MidI c st w sp yo D n q j) absorbTail := by
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r10]) absorbTail h).isSome =
      true := ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, h₂⟩ r hr => ?_) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.r4, h₂.r4]
  · rw [h₁.r5, h₂.r5]
  · exact h₁.env.pin h₂.env (by simp)

theorem absorb_ct {D : BitVec 32} {n q : Nat} (hq : q < 16) : CT (AbsI c st w sp yo D n q) (absorb yo) := by
  refine CT.seq (J := fun s => AbsI c st w sp yo D n q s ∧ s.z = decide (n = 0)) ?_
    (fun s ⟨k7, k8, H, x, hx, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 hs.r5 hs.data.lt32
    exact WP.of_runBlock ⟨s₁, run₁, ⟨k7, k8, H, x, hx, hs.keep hg₁ ⟨hm₁, hrd₁, hwr₁, hsp₁⟩⟩, hz⟩
  refine CT.ite (decide (n = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := MidI c st w sp yo D n q j₁) ((absorbFill_ct L hyo h0 hq).mono fun s h => h.1)
    (fun s ⟨⟨k7, k8, H, x, hx, hs⟩, _⟩ => WP.mono (absorbFill_ok L hyo hs h0) fun s' ⟨j, hj, hm⟩ =>
      ⟨k7, k8, H, x, s.mem, hx, by rw [hj, hx] at hm; exact hm⟩) ?_
  refine CT.seq (J := MidI c st w sp yo D n q (j₁ + 16 * ((n - j₁) / 16))) (absorbWhole_ct L hyo)
    (fun s ⟨k7, k8, H, x, m₀, hx, hs⟩ => WP.mono (whole_ok L hyo hs (hs.data_eq hyo)) fun s' ⟨j, hj, hm, _⟩ =>
      ⟨k7, k8, H, x, m₀, hx, by rw [hj] at hm; exact hm⟩) absorbTail_ct

/-- `ghash1 yo .r11 96`, of `T`. -/
theorem ghT_ct : CT (GhIn c st w sp .r11 96 (w + BitVec.ofNat 32 96)) (ghash1 yo .r11 tO) := by
  have eT := L.wA (d := 96) (by decide)
  have hf : (w + BitVec.ofNat 32 96).toNat + 16 ≤ 2 ^ 32 := by rw [L.wN (by decide)]; have := L.ww; omega
  refine ghash1_ct L hyo (.inr ⟨rfl, rfl⟩) hf ?_ ?_ ?_
  · rw [eT]; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · rw [eT]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [eT]; exact L.stk_w (by decide)

omit hyo in
theorem ghIn_T {s : State} {k7 k8 : BitVec 32} (he : Env c st w sp k7 k8 s) :
    GhIn c st w sp .r11 96 (w + BitVec.ofNat 32 96) s :=
  ⟨⟨k7, k8, he⟩, by rw [he.r11], by rw [L.wA (d := 96) (by decide)]; exact covers_left (he.perm.wC (by decide))⟩

/-- Before `flush yo`: `q` buffered bytes. -/
theorem flush_ct {q : Nat} (hq : q < 16) :
    CT (fun s => ∃ k7 k8, Env c st w sp k7 k8 s ∧ s.gpr .r6 = BitVec.ofNat 32 q) (flush yo) := by
  refine CT.seq (J := fun s => (∃ k7 k8, Env c st w sp k7 k8 s ∧ s.gpr .r6 = BitVec.ofNat 32 q) ∧
    s.z = decide (q = 0)) ?_ (fun s ⟨k7, k8, he, h6⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6]) (.block [.cmp .r6 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r6 h6 (by omega)
    exact WP.of_runBlock ⟨s₁, run₁, ⟨k7, k8, he.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁, by rw [hg₁, h6]⟩, hz⟩
  refine CT.ite (decide (q = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : q ≠ 0 := by simpa using hb
  refine CT.seq (J := GhIn c st w sp .r11 96 (w + BitVec.ofNat 32 96)) ?_ (fun s ⟨⟨k7, k8, he, h6⟩, _⟩ =>
    WP.mono (flushCopy_ok L hyo (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) ⟨he, rfl⟩ h6 hq h0)
      fun s' hm => ghIn_T L hm.env) (ghT_ct L hyo)
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6, .r10, .r11])
      (.seq (.block flushPre) copyLoop) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, h₁, a₁⟩, _⟩ ⟨⟨_, _, h₂, a₂⟩, _⟩ r hr => ?_) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a₁, a₂]
  · exact h₁.pin h₂ (by simp)
  · exact h₁.pin h₂ (by simp)

/-- `lens yo`: the lengths are not needed, only `W`. -/
theorem lens_ct : CT (fun s => ∃ k7 k8, Env c st w sp k7 k8 s) (lens yo) := by
  refine CT.seq (J := GhIn c st w sp .r11 96 (w + BitVec.ofNat 32 96)) ?_ (fun s ⟨k7, k8, he⟩ =>
    WP.mono (lensStore_ok L he) fun s' ⟨_, hg, hrd, hwr, hsp⟩ => ghIn_T L (k7 := k7) (k8 := k8)
      (he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide)) hsp hrd hwr)) (ghT_ct L hyo)
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r11])
      (.block (be64Store .r4 .r5 tO ++ be64Store .r6 .r7 (tO + 8))) h).isSome = true := ⟨_, by taint_decide⟩
  exact CT.taint _ (fun s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr => h₁.pin h₂ (by simp at hr; simp [hr])) hc

end

end VG.Proof.AesGcm.Arm
