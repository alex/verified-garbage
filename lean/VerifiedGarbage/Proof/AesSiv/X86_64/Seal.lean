import VerifiedGarbage.Proof.AesSiv.X86_64.Crypt

/-!
# AES-SIV on x86-64: `vg_aes_siv_seal`

The code saves the registers (`cryptPre_ok`), finishes S2V with the plaintext
into the first 16 bytes of the working space (`finish_wp`), sets the counter
from that IV (`counter_ok`), encrypts the data in place with CTR (`ctr_wp`)
and restores the registers: the working space then starts with the IV and
the data is the ciphertext (`seal_wp`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Proof.CmacAes.X86_64 (bytesAt_frame k0)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## What each step writes -/

theorem cryptMem_frame (h : Env s₀ C D P W R L) : Frame [⟨W, 2560⟩] s₀.mem (cryptMem s₀ P W L) :=
  ((Spill.saveMem_frame_base _ _ _ _ (fun p hp => by have := saved_le p hp; omega) (by have := h.wW; omega)).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base W (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base W (by decide) (by decide))

theorem cryptMem_saved : Spill.Saved (cryptMem s₀ P W L) W s₀.gpr saved :=
  ((Spill.saveMem_saved _ _ _ _ saved_slots).writeW _ (by decide) (by decide) (by decide)).writeW _ (by decide)
    (by decide) (by decide)

theorem cryptMem_data : (cryptMem s₀ P W L).readW (W + BitVec.ofNat 64 dataOff) 64 = P := by
  rw [cryptMem, Mem.readW_writeW_sep (Offset.sep W (d := dataOff) (n := 8) (e := lenOff) (k := 8) (by decide)
    (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]

theorem cryptMem_len : (cryptMem s₀ P W L).readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L := by
  rw [cryptMem, Mem.readW_writeW_self64]

/-- The regions the counter's two words are written to. -/
abbrev cntRegions (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 cntOff, 8⟩, ⟨W + BitVec.ofNat 64 (cntOff + 8), 8⟩]

theorem counter_frame (m : Mem) (W : Addr) (a b : BitVec 64) :
    Frame (cntRegions W) m ((m.writeW (W + BitVec.ofNat 64 cntOff) a).writeW (W + BitVec.ofNat 64 (cntOff + 8)) b) :=
  ((Frame.refl _ _).writeW List.mem_cons_self a (Region.contains_self (W + BitVec.ofNat 64 cntOff) 8)).writeW
    (List.mem_cons_of_mem _ List.mem_cons_self) b (Region.contains_self (W + BitVec.ofNat 64 (cntOff + 8)) 8)

/-! ## Ranges outside them -/

/-- A range of the working space outside what `finish` writes. -/
theorem fin_dis (h : Env s₀ C D P W R L) {out d n : Nat} (hout : out + 16 ≤ 256) (hd : d + n ≤ 2560)
    (h1 : out + 16 ≤ d ∨ d + n ≤ out) (h2 : d + n ≤ 32 ∨ 64 ≤ d) (h3 : d + n ≤ 144 ∨ 160 ≤ d)
    (h4 : d + n ≤ 224 ∨ 232 ≤ d) (h5 : d + n ≤ 256) :
    ∀ r ∈ finRegions W out (s₀.gpr .rsp), Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact (h.stk_w.sub_right (h.sW hd)).symm

/-- A region outside the working space and the stack, outside what `finish` writes. -/
theorem fin_out {X : Region} {out : Nat} (hout : out + 16 ≤ 256) (hw : X.Disjoint ⟨W, 2560⟩)
    (hs : (below (s₀.gpr .rsp) 16).Disjoint X) : ∀ r ∈ finRegions W out (s₀.gpr .rsp), X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Offset.sub_base W (by omega))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hs.symm

/-- A range of the working space outside what CTR writes. -/
theorem ctr_dis (h : Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 256) (h1 : d + n ≤ 64 ∨ 112 ≤ d) :
    ∀ r ∈ ctrRegions W P L (s₀.gpr .rsp), Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.p_w.symm.sub_left (h.sW (by omega))
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact (h.stk_w.sub_right (h.sW (by omega))).symm

/-- A region outside the data, the working space and the stack, outside what CTR writes. -/
theorem ctr_out {X : Region} (hp : X.Disjoint ⟨P, L⟩) (hw : X.Disjoint ⟨W, 2560⟩)
    (hs : (below (s₀.gpr .rsp) 16).Disjoint X) : ∀ r ∈ ctrRegions W P L (s₀.gpr .rsp), X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hs.symm

/-- A range of the working space outside the counter. -/
theorem cnt_dis {d n : Nat} (hd : d + n ≤ 2560) (h1 : d + n ≤ 64 ∨ 80 ≤ d) :
    ∀ r ∈ cntRegions W, Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [cntOff, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)

/-- A region outside the working space, outside the counter. -/
theorem cnt_out {X : Region} (hw : X.Disjoint ⟨W, 2560⟩) : ∀ r ∈ cntRegions W, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))

theorem one_out {X Y : Region} (hw : X.Disjoint Y) : ∀ r ∈ [Y], X.Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact hw

/-! ## The whole function -/

theorem seal_wp (v : Ctr32Impl) {s₀ : State} (h0 : sealX86_64.pre s₀) :
    WP isa («seal» v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ sealX86_64.post s₀ s' := by
  have h := Env.ofCrypt h0
  have ha := ArgRegs.ofCrypt h0
  have hcp := cryptPre_cp h0
  have hPw := cryptPre_pw h0
  show WP isa _ s₀ fun s' => gprPreserved s₀ s' ∧
    Spec.Siv.sealWith (Spec.Siv.ctxMac s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)
        (Spec.Siv.ctxCiph s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdx) 16)
        (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat) =
      (Spec.Aes.bytesAt s'.mem (s₀.gpr .r9) 16, Spec.Aes.bytesAt s'.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat)
  generalize s₀.gpr .rdi = C at h ha hcp ⊢
  generalize s₀.gpr .rdx = D at h ha ⊢
  generalize s₀.gpr .rcx = P at h ha hcp hPw ⊢
  generalize s₀.gpr .r9 = W at h ha ⊢
  generalize (s₀.gpr .rsi).toNat = R at h ha ⊢
  generalize (s₀.gpr .r8).toNat = L at h ha hcp hPw ⊢
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have hL : L ≤ 2 ^ 64 := by have := h.lt; omega
  obtain ⟨s₁, run₁, hr₁, m₁⟩ := cryptPre_ok h ha
  have f₁ : Frame [⟨W, 2560⟩] s₀.mem s₁.mem := m₁ ▸ cryptMem_frame h
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (finish_wp v h hr₁ (Or.inl rfl)) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := counter_ok h h₂.regs.r15 h₂.regs.rd h₂.regs.wr
  have f₃ : Frame (cntRegions W) s₂.mem s₃.mem := m₃ ▸ counter_frame _ _ _ _
  have hr₃ : Regs s₀ C D P W R L s₃ := h₂.regs.keep (fun r hr => g₃ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) rd₃ wr₃
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  -- The data pointer and its length, kept since the save.
  have hslot {d : Nat} (hd : 208 ≤ d) (hd' : d + 8 ≤ 224) :
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [f₃.readW (Region.contains_self _ _) (cnt_dis (by omega) (by omega)) (by decide),
      f₂.readW (Region.contains_self _ _) (fin_dis h (by decide) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) (by decide)]
  have h208 : s₃.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P := by
    rw [hslot (by decide) (by decide), m₁, cryptMem_data]
  have h216 : s₃.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L := by
    rw [hslot (by decide) (by decide), m₁, cryptMem_len]
  have hcnt : ∃ hi lo : BitVec 64, s₃.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
      s₃.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt s₂.mem W 16)) := by
    rw [m₃]; exact counter_cnt s₂.mem W
  refine WP.seq (WP.mono (ctr_wp v h hcp hPw hr₃ hcnt h208 h216) fun s₄ h₄ => ?_)
  have f₄ := h₄.frame
  -- The saved registers.
  have hsv₄ : Spill.Saved s₄.mem W s₀.gpr saved := by
    have hb (p : Reg × Nat) (hp : p ∈ saved) : 160 ≤ p.2 ∧ p.2 + 8 ≤ 208 := ⟨saved_ge p hp, saved_le p hp⟩
    refine ((((m₁ ▸ cryptMem_saved).frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame f₄ fun p hp => ?_)
    · have := hb p hp
      exact fin_dis h (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · have := hb p hp; exact cnt_dis (by omega) (by omega)
    · have := hb p hp; exact ctr_dis h (by omega) (by omega)
  refine WP.mono (Spill.restore_ok .r15 saved s₀.gpr s₄ (by decide) (fun p hp => by
      rw [h₄.regs.r15, h₄.regs.rd, h₄.regs.wr]; exact h.inRW rfl rfl (by have := saved_le p hp; omega))
    (by rw [h₄.regs.r15]; exact hsv₄)) fun s₅ ⟨h₅a, h₅b, m₅, _, _⟩ => ?_
  -- The IV: S2V's end, from the arguments.
  have hv : Spec.Aes.bytesAt s₅.mem W 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s₀.mem C R) (Spec.Aes.bytesAt s₀.mem D 16) (Spec.Aes.bytesAt s₀.mem P L) := by
    have o₂ := h₂.out
    rw [k0] at o₂
    have c₀ := ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
    have d₀ := cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
    rw [k0] at c₀ d₀
    rw [m₅, bytesAt_frame f₄ c₀ (by decide), bytesAt_frame f₃ d₀ (by decide), o₂,
      ctxMac_frame f₁ (one_out h.c_w) hRb, bytesAt_frame f₁ (one_out h.d_w) (by decide),
      bytesAt_frame f₁ (one_out h.p_w) hL]
  -- The ciphertext: CTR of the data from the IV's counter.
  have hc : Spec.Aes.bytesAt s₅.mem P L =
      Spec.Siv.ctr (Spec.Siv.ctxCiph s₀.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s₅.mem W 16))
        (Spec.Aes.bytesAt s₀.mem P L) := by
    have c₀ := ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
    have d₀ := cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
    rw [k0] at c₀ d₀
    rw [m₅, h₄.data, bytesAt_frame f₄ c₀ (by decide), bytesAt_frame f₃ d₀ (by decide),
      ctxCiph_frame f₃ (cnt_out h.c_w) hRb, ctxCiph_frame f₂ (fin_out (by decide) h.c_w h.stk_c) hRb,
      ctxCiph_frame f₁ (one_out h.c_w) hRb, bytesAt_frame f₃ (cnt_out h.p_w) hL,
      bytesAt_frame f₂ (fin_out (by decide) h.p_w h.stk_p) hL, bytesAt_frame f₁ (one_out h.p_w) hL]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hsp : r = .rsp
    · subst hsp; rw [h₅b _ (by decide), h₄.regs.rsp]
    · exact h₅a r (saved_all r hr hsp)
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    have hw := h.ret_w
    have hb := Offset.base_disjoint_below (s₀.gpr .rsp) (n := 16) (k := 8) (by decide)
    rw [m₅, f₄.readW c (ctr_out h.ret_p hw hb.symm) (by decide), f₃.readW c (cnt_out hw) (by decide),
      f₂.readW c (fin_out (by decide) hw hb.symm) (by decide), f₁.readW c (one_out hw) (by decide)]
  · rw [hc, hv]
    rfl

end VG.Proof.AesSiv.X86_64
