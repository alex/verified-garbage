import VerifiedGarbage.Proof.AesGcm.X86.Top

/-!
# AES-GCM on x86: the ciphertext into GHASH (`textAbsorb`)

Untrusted: everything here is checked by Lean. `textAbsorb` absorbs the
`len` bytes at `data` (the ciphertext) into GHASH, after padding the
additional data if they are the first text (`textAbsorb_pc`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ghashInput)
open VG.Proof.Gcm (Absorbed)

theorem append_toNat32 (hi lo : BitVec 32) : (hi ++ lo).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

/-- No text so far: both words of its length are 0. -/
theorem nil_of_len {xl xh : BitVec 32} {c : List Byte} (ht : (xh ++ xl).toNat = c.length) :
    (xl ||| xh == 0) = decide (c = []) := by
  rw [append_toNat32] at ht
  by_cases hc : c = []
  · subst hc
    have h0 : xl = 0 ∧ xh = 0 :=
      ⟨BitVec.eq_of_toNat_eq (by simp at ht ⊢; omega), BitVec.eq_of_toNat_eq (by simp at ht ⊢; omega)⟩
    obtain ⟨rfl, rfl⟩ := h0
    rfl
  · have hl : c.length ≠ 0 := fun h => hc (List.eq_nil_of_length_eq_zero h)
    simp only [hc, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_or] at this
    obtain ⟨h1, h2⟩ := Nat.or_eq_zero_iff.mp this
    omega

/-- The regions `textAbsorb` writes. -/
abbrev taFrame (St W SP : BitVec 32) (K : Nat) : List Region :=
  [⟨w64 St + BitVec.ofNat 64 16, 32⟩, ⟨w64 W + BitVec.ofNat 64 96, 16⟩, wsR W, below SP K]

/-- The kept values `textAbsorb` reads. -/
structure TaSl (W : BitVec 32) (D : BitVec 32) (n : Nat) (al xl xh : BitVec 32) (m : Mem) : Prop where
  data : slotv m W dataO = D
  len : slotv m W lenO = BitVec.ofNat 32 n
  al : slotv m W alO = al
  xl : slotv m W xlO = xl
  xh : slotv m W xhO = xh

theorem TaSl.frame {W D : BitVec 32} {n : Nat} {al xl xh : BitVec 32} {m m' : Mem} (h : TaSl W D n al xl xh m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (keptR W).Disjoint r) : TaSl W D n al xl xh m' := by
  have k : ∀ {o}, 128 ≤ o → o + 4 ≤ 240 → slotv m' W o = slotv m W o := fun h₁ h₂ =>
    slot_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))
  exact ⟨by rw [k (by decide) (by decide)]; exact h.data, by rw [k (by decide) (by decide)]; exact h.len,
    by rw [k (by decide) (by decide)]; exact h.al, by rw [k (by decide) (by decide)]; exact h.xl,
    by rw [k (by decide) (by decide)]; exact h.xh⟩

/-- Before `textAbsorb`: `n` bytes of text at `D`. -/
structure TaIn (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) (al xl xh : BitVec 32) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  sl : TaSl W D n al xl xh s.mem
  nlt : n < 2 ^ 32
  data : DataOk St W SP K s D n

/-- What GHASH absorbs of a message with additional data `a` and text `c`, of the lengths kept. -/
abbrev TaLen (al ah xl xh : BitVec 32) (a c : List Byte) : Prop :=
  ah ++ al = BitVec.ofNat 64 a.length ∧ (xh ++ xl).toNat = c.length

/-- After `textAbsorb`, from `m₀`. -/
structure TaOut (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) (al ah xl xh : BitVec 32) (m₀ : Mem)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  frame : Frame (taFrame St W SP K) m₀ s.mem
  abs : ∀ a c, TaLen al ah xl xh a c →
    Absorbed m₀ (w64 St + BitVec.ofNat 64 16) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx) (ghashInput a c) →
    Absorbed s.mem (w64 St + BitVec.ofNat 64 16) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx)
      (ghashInput a (c ++ bytesAt m₀ (w64 D) n))

/-- After the padding of the additional data, if the text so far is empty. -/
structure TaMid (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) (al ah xl xh : BitVec 32) (m₀ : Mem)
    (s : State) : Prop where
  ta : TaIn Ctx St W SP K D n al xl xh s
  hk : Hk s.mem Ctx = Hk m₀ Ctx
  bytes : bytesAt s.mem (w64 D) n = bytesAt m₀ (w64 D) n
  frame : Frame (taFrame St W SP K) m₀ s.mem
  abs : ∀ a c, TaLen al ah xl xh a c →
    Absorbed m₀ (w64 St + BitVec.ofNat 64 16) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx) (ghashInput a c) →
    Absorbed s.mem (w64 St + BitVec.ofNat 64 16) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx)
      (if c = [] then a ++ zeros (padLen a.length) else ghashInput a c)

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K)
include L

theorem kept_taFrame : ∀ r ∈ taFrame St W SP K, (keptR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem ctx_taFrame : ∀ r ∈ taFrame St W SP K, (⟨w64 Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw.sub_right (Lay.wSub (by decide))
  · exact L.cw.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

omit L in
theorem data_taFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataOk St W SP K s D n) :
    ∀ r ∈ taFrame St W SP K, (⟨w64 D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.stk.symm

omit L in
theorem abs_taFrame {m m' : Mem} (h : Frame (absFrame St W SP K 16) m m') : Frame (taFrame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨wsR W, by simp, fun _ h => h⟩
    · exact ⟨below SP K, by simp, fun _ h => h⟩

omit L in
theorem t_taFrame {m m' : Mem} (h : Frame (tFrame St W SP K 16) m m') : Frame (taFrame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨wsR W, by simp, fun _ h => h⟩
    · exact ⟨below SP K, by simp, fun _ h => h⟩

omit L in
theorem pslot_taFrame {m m' : Mem} (h : Frame [pslotR W] m m') : Frame (taFrame St W SP K) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wsR W, by simp, pslot_ws W⟩

omit L in
theorem ta_keep {D : BitVec 32} {n : Nat} {al xl xh : BitVec 32} {s s' : State}
    (h : TaIn Ctx St W SP K D n al xl xh s) (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi)
    (hsp : s'.gpr .esp = s.gpr .esp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    TaIn Ctx St W SP K D n al xl xh s' :=
  ⟨h.env.keep hbp hsi hsp hrd hwr (by rw [hm]), by rw [hm]; exact h.sl, h.nlt, h.data.of_eq hrd hwr⟩

theorem textAbsorb_pc {D : BitVec 32} {n : Nat} {al ah xl xh : BitVec 32} :
    Pc (fun (m₀ : Mem) s => TaIn Ctx St W SP K D n al xl xh s ∧ s.mem = m₀) textAbsorb
      (TaOut Ctx St W SP K D n al ah xl xh ·) := by
  by_cases hnlt : n < 2 ^ 32
  swap
  · exact Pc.vacuous fun _ _ h => hnlt h.1.nlt
  refine Pc.seq (Q := fun m₀ s => (TaIn Ctx St W SP K D n al xl xh s ∧ s.mem = m₀) ∧ s.zf = some (decide (n = 0)))
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => WP.mono (test_ok L h.env .eax lenO (by decide) h.sl.len h.nlt)
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨ta_keep h (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) m rd wr,
          by rw [m, hm]⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (n = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨h.env, by rw [hm]; exact Frame.refl _ _,
      fun a c _ ha => ?_⟩
    rw [hm]; simpa [bytesAt] using ha
  have hn0 : n ≠ 0 := by simpa using hf
  -- Whether there is text so far.
  refine Pc.seq (Q := fun m₀ s => (TaIn Ctx St W SP K D n al xl xh s ∧ s.mem = m₀) ∧
      s.zf = some (xl ||| xh == 0))
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨h, hm⟩, _⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.env.ebp, h₂.1.1.env.ebp]) (by taint_decide)) ?_
  · have he := h.env
    have h1 := h.sl.xl; have h2 := h.sl.xh
    rw [slotv_eq] at h1 h2
    exact WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn', h1, h2], ⟨ta_keep h (by regs []) (by regs [])
      (by regs []) (by mems []) (by mems []) (by mems []), by mems []; exact hm⟩, by mems []⟩
  -- The padding of the additional data, before the first text.
  refine Pc.seq (Q := TaMid Ctx St W SP K D n al ah xl xh) ?_ ?_
  · refine Pc.ite (xl ||| xh == 0) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
    · refine Pc.seq (Q := fun m₀ s => TaIn Ctx St W SP K D n al xl xh s ∧
          slotv s.mem W bO = BitVec.ofNat 32 (al.toNat % 16) ∧ Frame [⟨w64 W + BitVec.ofNat 64 bO, 4⟩] m₀ s.mem)
        (Pc.taint [.ebp] (fun m₀ s ⟨⟨h, hm⟩, _⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.env.ebp, h₂.1.1.env.ebp]) (by taint_decide)) ?_
      · have he := h.env
        have h1 := h.sl.al
        rw [slotv_eq] at h1
        have hand := and15 al
        refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn, he.wIn', h1], ?_⟩
        have fb : Frame [⟨w64 W + BitVec.ofNat 64 bO, 4⟩] s.mem
            (s.mem.writeW (w64 W + BitVec.ofNat 64 bO) (al &&& BitVec.ofNat 32 15)) :=
          (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
        have dK : ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 bO, 4⟩ : Region)], (keptR W).Disjoint r := fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        refine ⟨⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by
            simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact slot_frame fb fun r hr =>
              (dK r hr).sub_left (Offset.sub _ (by decide) (by decide))),
          by simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact h.sl.frame fb dK, h.nlt,
          h.data.of_eq (by mems []) (by mems [])⟩, ?_, ?_⟩
        · simp only [mem_setMem, mem_setReg, mem_arithFlags, slotv_eq, Mem.readW_writeW_self32]; exact hand
        · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [← hm]; exact fb
      refine Pc.mono (Pc.lift (flush_pc L (yo := 16) (.inr rfl) (b := al.toNat % 16) (Nat.mod_lt _ (by decide)))
        (fun _ s => s.mem) fun m₀ s h => ⟨⟨h.1.env, h.2.1⟩, rfl⟩) (fun _ _ h => h)
        fun m₀ s' ⟨s, ⟨h, _, fb⟩, fo, rd, wr⟩ => ?_
      have dS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 bO, 4⟩ : Region)],
          (⟨w64 St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
      have kT : ∀ r ∈ tFrame St W SP K 16, (keptR W).Disjoint r := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w (by decide)).symm
      have hHs : Hk s.mem Ctx = Hk m₀ Ctx := blockAt_frame fb fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
      have hH' : Hk s'.mem Ctx = Hk s.mem Ctx := blockAt_frame fo.frame (ctx_tFrame L (.inr rfl))
      have dT : ∀ r ∈ tFrame St W SP K 16, (⟨w64 D, n⟩ : Region).Disjoint r := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact h.data.st.sub_right (Lay.stSub (by decide))
        · exact h.data.w.sub_right (Lay.wSub (by decide))
        · exact h.data.w.sub_right (Lay.wSub (by decide))
        · exact h.data.stk.symm
      have hfit := h.data.fit
      refine ⟨⟨fo.env, h.sl.frame fo.frame kT, h.nlt, h.data.of_eq rd wr⟩, by rw [hH', hHs], ?_, ?_,
        fun a c ⟨hl, hx⟩ ha => ?_⟩
      · rw [bytesAt_frame fo.frame dT (by omega), bytesAt_frame fb (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.data.w.sub_right (Lay.wSub (by decide))) (by omega)]
      · exact (fb.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩).trans (t_taFrame fo.frame)
      · have hc : c = [] := by
          have := nil_of_len hx; rw [ht] at this; simpa using this.symm
        subst hc
        simp only [↓reduceIte]
        rw [Proof.Gcm.ghashInput_nil] at ha
        have ha₁ : Absorbed s.mem (w64 St + BitVec.ofNat 64 16) (w64 St + BitVec.ofNat 64 32) (Hk s.mem Ctx) a := by
          rw [hHs]
          exact ha.congr (blockAt_frame fb (dS (by decide))) (bytesAt_frame fb (dS (d := 32) (k := a.length % 16)
            (by omega)) (by omega))
        have := fo.abs a (lo_mod16 hl).symm ha₁
        rwa [hHs] at this
    · refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨h, by rw [hm], by rw [hm],
        by rw [hm]; exact Frame.refl _ _, fun a c ⟨_, hx⟩ ha => ?_⟩
      have hc : c ≠ [] := by
        have := nil_of_len hx; rw [hf] at this; simpa using this.symm
      simp only [hc, ↓reduceIte]; rw [hm]; exact ha
  -- The text, as the piece `absorb` takes it.
  refine Pc.seq (Q := fun m₀ s => ∃ s₃, TaMid Ctx St W SP K D n al ah xl xh m₀ s₃ ∧
      AbsIn Ctx St W SP K D n (xl.toNat % 16) s ∧ Frame [pslotR W] s₃.mem s.mem ∧ s.rd = s₃.rd ∧ s.wr = s₃.wr)
    (Pc.taint [.ebp] (fun m₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ta.env.ebp, h₂.ta.env.ebp]) (by taint_decide)) ?_
  · have he := h.ta.env
    have h1 := h.ta.sl.data; have h2 := h.ta.sl.len; have h3 := h.ta.sl.xl
    rw [slotv_eq] at h1 h2 h3
    simp only [dataO, lenO, xlO] at h1 h2 h3
    have hand := and15 xl
    refine WP.of_runBlock ⟨_, by xrun [setText, he.ebp, L.aW, he.wIn, he.wIn', h1, h2, h3], s, h, ?_⟩
    refine ⟨⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems []), ?_, ?_, ?_,
        Nat.mod_lt _ (by decide), h.ta.nlt, h.ta.data.of_eq (by mems []) (by mems [])⟩, ?_, by mems [], by mems []⟩
    rotate_left 3
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]
      exact pslot_write (pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide)
        (by decide) _) (by decide) (by decide) _
    · mems [slotv_eq]
    · mems [slotv_eq, h2]
    · mems [slotv_eq, h3]; rw [hand]
  refine Pc.mono (Pc.lift (absorb_pc L (yo := 16) (.inr rfl) (b := xl.toNat % 16) (Nat.mod_lt _ (by decide)) hnlt)
    (fun _ s => s.mem) fun m₀ s ⟨_, _, h, _⟩ => ⟨h, rfl⟩) (fun _ _ h => h)
    fun m₀ s' ⟨s, ⟨s₃, h₃, _, fr, _, _⟩, ao, _, _⟩ => ?_
  have hd := h₃.ta.data
  have hfit := hd.fit
  have hD : bytesAt s.mem (w64 D) n = bytesAt m₀ (w64 D) n := by
    rw [bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd.w.sub_right (Lay.wSub (by decide))) (by omega),
      h₃.bytes]
  have hHs : Hk s.mem Ctx = Hk m₀ Ctx := by
    rw [← h₃.hk]; exact blockAt_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  refine ⟨ao.env, (h₃.frame.trans (pslot_taFrame fr)).trans (abs_taFrame ao.frame), fun a c ⟨hl, hx⟩ ha => ?_⟩
  have hx' : (if c = [] then a ++ zeros (padLen a.length) else ghashInput a c).length % 16 = xl.toNat % 16 := by
    have e := append_toNat32 xh xl
    split
    · next hc =>
      subst hc
      simp only [List.length_nil] at hx
      rw [List.length_append, Proof.Gcm.length_zeros, Proof.Gcm.length_pad_mod]
      omega
    · next hc =>
      rw [Proof.Gcm.ghashInput_of_ne hc]
      simp only [List.length_append, Proof.Gcm.length_zeros]
      have := Proof.Gcm.length_pad_mod a.length
      omega
  have := ao.abs _ hx' (by rw [hHs]; exact absorbed_pslot fr (h₃.abs a c ⟨hl, hx⟩ ha) L (.inr rfl))
  rw [hHs, hD, ← Proof.Gcm.ghashInput_append a c _ (by
    intro h0; have := congrArg List.length h0; rw [length_bytesAt] at this; exact hn0 this)] at this
  exact this

end

end VG.Proof.AesGcm.X86
