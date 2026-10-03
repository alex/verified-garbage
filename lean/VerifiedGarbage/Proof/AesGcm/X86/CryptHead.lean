import VerifiedGarbage.Proof.AesGcm.X86.Crypt

/-!
# AES-GCM on x86: the rest of the keystream block (`cryptHead`)

Untrusted: everything here is checked by Lean. With `P mod 16 ≠ 0` bytes of
the keystream block used, `cryptHead` XORs the next `min (16 - P mod 16, n)`
into the data (`cryptHead_pc`), by `Proof.Gcm.ctr_head`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K) {R : Nat} {icb : Block}
  {D : BitVec 32} {n P : Nat}
include L

/-- After the block that sets up the XOR. -/
structure CHead2 (k : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  edi : s.gpr .edi = D
  edx : s.gpr .edx = St + BitVec.ofNat 32 (64 + P % 16)
  ecx : s.gpr .ecx = BitVec.ofNat 32 k
  dO : slotv s.mem W dO = D + BitVec.ofNat 32 k
  nO : slotv s.mem W nO = BitVec.ofNat 32 (n - k)
  fr : Frame [pslotR W] m₀ s.mem
  data : DataW Ctx St W SP K s D n
  nlt : n < 2 ^ 32
  r0 : RoundsAt m₀ W R

theorem cHead2_ok (k : Nat) (hk : k ≤ n) (m₀ : Mem) {s : State} (h : CrIn Ctx St W SP K R D n P s)
    (hm : s.mem = m₀) {s₁ : State} (hs₁ : MinOut k s s₁) :
    WP isa (.block [.mov .edi (slot dO), .mov .edx (.reg .esi), .alu .add .edx (imm 64), .alu .add .edx (slot bO),
      .mov .eax (slot nO), .alu .sub .eax (.reg .ecx), .store (at_ .ebp nO) .eax,
      .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store (at_ .ebp dO) .eax]) s₁
      (CHead2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (D := D) (n := n) (P := P) k m₀) := by
  have he := h.env
  have he₁ : Env Ctx St W SP s₁ := he.keep (hs₁.other _ (by decide) (by decide))
    (hs₁.other _ (by decide) (by decide)) (hs₁.other _ (by decide) (by decide)) hs₁.rd hs₁.wr (by rw [hs₁.mem])
  have hd : slotv s₁.mem W dO = D := by rw [hs₁.mem]; exact h.dO
  have hn : slotv s₁.mem W nO = BitVec.ofNat 32 n := by rw [hs₁.mem]; exact h.nO
  have hb : slotv s₁.mem W bO = BitVec.ofNat 32 (P % 16) := by rw [hs₁.mem]; exact h.bO
  have hc := hs₁.ecx
  have esub : BitVec.ofNat 32 n - BitVec.ofNat 32 k = BitVec.ofNat 32 (n - k) := ofNat_sub32 hk h.nlt
  refine WP.of_runBlock ⟨_, by xrun [he₁.ebp, he₁.esi, L.aW, he₁.wIn, he₁.wIn', hd, hn, hb, hc], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.nlt, by rw [← hm]; exact h.rounds⟩
  · exact he₁.keep (by regs []) (by regs []) (by regs []) rfl rfl (by mems [])
  · regs [hd]
  · regs [he₁.esi, add_ofNat_assoc32]
  · regs [hc]
  · mems [slotv_eq, hd, hc]
  · mems [slotv_eq, hn, hc, esub]
  · simp only [mem_setMem, gpr_setMem, mem_setReg, mem_arithFlags, ← hs₁.mem, ← hm]
    exact pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide) (by decide) _
  · exact h.data.of_eq (by mems [hs₁.rd]) (by mems [hs₁.wr])

/-- The XOR with the rest of the keystream block. -/
theorem cHead3_ok (k : Nat) (hkn : k ≤ n) (hk1 : 1 ≤ k) (hbk : P % 16 + k ≤ 16) (hw : k = n ∨ P % 16 + k = 16)
    (hP : P % 16 ≠ 0) (m₀ : Mem) {s : State}
    (h : CHead2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (D := D) (n := n) (P := P) k m₀ s) :
    WP isa xorLoop s (CrMid Ctx St W SP K R icb D n P m₀ k) := by
  have he := h.env
  have eS := L.aS (o := 64 + P % 16) (by omega)
  have dk := h.data.take hkn
  have xp : XorPre s (St + BitVec.ofNat 32 (64 + P % 16)) D k := by
    refine ⟨h.edx, h.edi, h.ecx, hk1, by have := h.nlt; omega, ?_, dk.ok.fit, ?_, dk.wr, ?_⟩
    · rw [L.nS (by omega)]; have := L.fs; omega
    · rw [eS]; exact covers_left (he.stC (by omega))
    · rw [eS]; exact (dk.ok.st.sub_right (Lay.stSub (by omega))).symm
  refine WP.mono (xorLoop_ok s xp) fun s' c => ?_
  have cm := c.mem
  rw [eS] at cm
  have hxl := length_xorBytes s.mem (w64 D) (w64 St + BitVec.ofNat 64 (64 + P % 16)) k
  have fw : Frame [⟨w64 D, k⟩] s.mem s'.mem := by rw [cm]; exact writeBytes_frame' _ hxl
  have fw' : Frame [⟨w64 D + BitVec.ofNat 64 0, k⟩] s.mem s'.mem := by simpa using fw
  have hf₁ : Frame (crFrame St W SP K D n) s.mem s'.mem := part_crFrame (j := 0) (by omega) fw'
  have hf : Frame (crFrame St W SP K D n) m₀ s'.mem := (pslot_crFrame h.fr).trans hf₁
  have hlt := h.nlt
  -- What the XOR writes is apart from the state and the slots.
  have dS : ∀ {a l : Nat}, a + l ≤ 80 → ∀ r ∈ [(⟨w64 D, k⟩ : Region)], (⟨w64 St + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r :=
    fun hal r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dk.ok.st.sub_right (Lay.stSub hal)).symm
  have dW : ∀ {o : Nat}, o + 4 ≤ 2560 → ∀ r ∈ [(⟨w64 D, k⟩ : Region)], (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r :=
    fun ho r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dk.ok.w.sub_right (Lay.wSub ho)).symm
  have pS : ∀ {a l : Nat}, a + l ≤ 80 → ∀ r ∈ [pslotR W], (⟨w64 St + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r :=
    fun hal r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.st_w hal (.inr ⟨by decide, by decide⟩)
  have pD : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [pslotR W], (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r :=
    fun hal r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.data.ok.w.sub_left (Offset.sub_base _ hal)).sub_right (Lay.wSub (by decide))
  have pD0 : ∀ r ∈ [pslotR W], (⟨w64 D, k⟩ : Region).Disjoint r := by
    have := pD (a := 0) (l := k) (by omega); simpa using this
  refine ⟨⟨env_crFrame L h.data he hf₁ (c.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (c.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (c.other _ (by decide) (by decide) (by decide) (by decide) (by decide)) c.rd c.wr, hkn, hlt,
    h.data.of_eq c.rd c.wr, rounds_frame hf (kept_crFrame L h.data) h.r0, fun hc => ?_, fun hc => ?_, ?_, ?_, hf⟩,
    ?_, ?_⟩
  · refine (hc.head hP hbk).congr ?_ ?_
    · rw [blockAt_frame fw (dS (by decide)), blockAt_frame h.fr (pS (by decide))]
    · rw [blockAt_frame fw (dS (by decide)), blockAt_frame h.fr (pS (by decide))]
  · have e := bytesAt_writeBytes_self s.mem (w64 D) (xorBytes s.mem (w64 D) (w64 St + BitVec.ofNat 64 (64 + P % 16)) k)
      (by rw [hxl]; omega)
    rw [hxl] at e
    rw [cm, e, xorBytes, bytesAt_frame h.fr pD0 (by omega), bytesAt_frame h.fr (pS (by omega)) (by omega)]
    have := Proof.Gcm.ctr_head hc hP (d := bytesAt m₀ (w64 D) k) (by rw [length_bytesAt]; exact hbk)
    rw [length_bytesAt, add_ofNat_assoc] at this
    exact this
  · rw [bytesAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (split_disj (by omega)).symm) (by omega),
      bytesAt_frame h.fr (pD (by omega)) (by omega)]
  · rcases hw with hw | hw
    · left; omega
    · right; omega
  · rw [slotv_eq, slot_frame fw (dW (by decide))]; exact h.dO
  · rw [slotv_eq, slot_frame fw (dW (by decide))]; exact h.nO

theorem cryptHead_pc (hn0 : n ≠ 0) (hP : P % 16 ≠ 0) :
    Pc (fun (m₀ : Mem) s => CrIn Ctx St W SP K R D n P s ∧ s.mem = m₀) cryptHead
      (CrMid Ctx St W SP K R icb D n P · (min (16 - P % 16) n)) := by
  have hb16 : P % 16 < 16 := Nat.mod_lt _ (by decide)
  generalize hk : min (16 - P % 16) n = k
  have hkn : k ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  have hbk : P % 16 + k ≤ 16 := by omega
  have hw : k = n ∨ P % 16 + k = 16 := by omega
  refine Pc.seq (Q := fun m₀ s₁ => ∃ s, (CrIn Ctx St W SP K R D n P s ∧ s.mem = m₀) ∧ MinOut k s s₁)
    (hk ▸ Pc.of (I := CrIn Ctx St W SP K R D n P) (R := MinOut (min (16 - P % 16) n))
      (fun s h => minLen_ok L h.env h.nO h.bO (by omega) h.nlt)
      (minLen_ct fun s h => ⟨h.env.ebp, Ctx, St, SP, K, L, h.env, h.nO, h.bO, by omega, h.nlt⟩)
      _ fun _ _ h => h.1) ?_
  refine Pc.seq (Q := CHead2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (D := D) (n := n)
      (P := P) k)
    (Pc.taint [.ebp, .esi] (fun m₀ s₁ ⟨s, ⟨h, hm⟩, hs₁⟩ => cHead2_ok L k hkn m₀ h hm hs₁)
      (fun _ _ s₁ s₂ ⟨t₁, ⟨h₁, _⟩, g₁⟩ ⟨t₂, ⟨h₂, _⟩, g₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [g₁.other _ (by decide) (by decide), g₂.other _ (by decide) (by decide), h₁.env.ebp, h₂.env.ebp]
        · rw [g₁.other _ (by decide) (by decide), g₂.other _ (by decide) (by decide), h₁.env.esi, h₂.env.esi])
      (by taint_decide)) ?_
  exact Pc.taint [.edi, .edx, .ecx] (fun m₀ s h => cHead3_ok L k hkn hk1 hbk hw hP m₀ h)
    (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.edi, h₂.edi]
      · rw [h₁.edx, h₂.edx]
      · rw [h₁.ecx, h₂.ecx])
    (by taint_decide)

end

end VG.Proof.AesGcm.X86
