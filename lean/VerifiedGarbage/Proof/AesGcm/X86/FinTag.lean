import VerifiedGarbage.Proof.AesGcm.X86.Tag
import VerifiedGarbage.Proof.AesGcm.X86.Top

/-!
# AES-GCM on x86: the tag of a streaming state (`finTag`)

Untrusted: everything here is checked by Lean. `finTag o` pads what GHASH
buffered (`text_len mod 16` bytes, or `aad_len mod 16` if there is no text)
and absorbs it (`flush 16`), then writes the tag to `W + o` (`tag`): the
full tag of the message the state represents (`finTag_pc`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes toBytes StreamRepr fullTag ghashInput)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem lensBlock_mod (a t : Nat) : lensBlock (a % 2 ^ 64) t = lensBlock a t := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (a % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * a)]
  congr 2
  omega

theorem val64_eq (lo hi : BitVec 32) : val64 lo hi = (hi ++ lo).toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

/-- The length of what GHASH buffered, modulo 16. -/
theorem ghashInput_mod {a c : List Byte} :
    (ghashInput a c).length % 16 = (if c = [] then a.length else c.length) % 16 := by
  by_cases hc : c = []
  · simp [ghashInput, hc]
  · rw [Proof.Gcm.ghashInput_of_ne hc]
    simp only [hc, ↓reduceIte, List.length_append, Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod a.length
    omega

theorem or_eq_zero32 (a b : BitVec 32) : (a ||| b = 0) ↔ (a = 0 ∧ b = 0) := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_or] at this
    have := Nat.or_eq_zero_iff.mp this
    exact ⟨BitVec.eq_of_toNat_eq (by simpa using this.1), BitVec.eq_of_toNat_eq (by simpa using this.2)⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Which length's remainder GHASH buffered: `text_len`'s, or `aad_len`'s if there is no text. -/
theorem buffered_mod {al ah xl xh : BitVec 32} {a c : List Byte} (hl : ah ++ al = BitVec.ofNat 64 a.length)
    (ht : (xh ++ xl).toNat = c.length) :
    (ghashInput a c).length % 16 = (if (xl ||| xh == 0) = true then al else xl).toNat % 16 := by
  rw [ghashInput_mod]
  have e := val64_eq xl xh
  simp only [val64] at e
  by_cases hc : c = []
  · subst hc
    have h0 : xl = 0 ∧ xh = 0 := by
      simp only [List.length_nil] at ht
      exact ⟨BitVec.eq_of_toNat_eq (by simp; omega), BitVec.eq_of_toNat_eq (by simp; omega)⟩
    obtain ⟨rfl, rfl⟩ := h0
    simp only [↓reduceIte, BitVec.or_self, beq_self_eq_true]
    exact (lo_mod16 hl).symm
  · have hne : (xl ||| xh == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, or_eq_zero32]
      rintro ⟨rfl, rfl⟩
      exact hc (List.eq_nil_of_length_eq_zero (by simp at ht; omega))
    simp only [hc, ↓reduceIte, hne, Bool.false_eq_true]
    omega

/-- The kept lengths and rounds `finTag` reads. -/
structure FinIn (Ctx St W SP : BitVec 32) (R : Nat) (al ah xl xh : BitVec 32) (s : State) : Prop where
  env : Env Ctx St W SP s
  al : slotv s.mem W alO = al
  ah : slotv s.mem W ahO = ah
  xl : slotv s.mem W xlO = xl
  xh : slotv s.mem W xhO = xh
  rounds : RoundsAt s.mem W R

/-- After `finTag o`: the tag of what the state represented, from `m₀`. -/
structure FinOut (Ctx St W SP : BitVec 32) (R o : Nat) (al ah xl xh : BitVec 32) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  rounds : RoundsAt s.mem W R
  frame : Frame (tagFrame St W SP o) m₀ s.mem
  tag : ∀ iv a c, StreamRepr m₀ (w64 St) (ciphOf m₀ Ctx R) (Hk m₀ Ctx) iv a c → ah ++ al = BitVec.ofNat 64 a.length →
    (xh ++ xl).toNat = c.length → bytesAt s.mem (w64 W + BitVec.ofNat 64 o) 16 = fullTag (ciphOf m₀ Ctx R) (Hk m₀ Ctx) iv a c

theorem FinIn.keep {Ctx St W SP : BitVec 32} {R : Nat} {al ah xl xh : BitVec 32} {s s' : State}
    (h : FinIn Ctx St W SP R al ah xl xh s) (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi)
    (hsp : s'.gpr .esp = s.gpr .esp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    FinIn Ctx St W SP R al ah xl xh s' :=
  ⟨h.env.keep hbp hsi hsp hrd hwr (by rw [hm]), by rw [hm]; exact h.al, by rw [hm]; exact h.ah, by rw [hm]; exact h.xl,
    by rw [hm]; exact h.xh, by rw [hm]; exact h.rounds⟩

section
variable {Ctx St W SP : BitVec 32} (L : Lay Ctx St W SP 28)
include L

theorem finTag_pc {R o : Nat} (ho : o = 0 ∨ o = 112) {al ah xl xh : BitVec 32} :
    Pc (fun (m₀ : Mem) s => FinIn Ctx St W SP R al ah xl xh s ∧ s.mem = m₀) (finTag vg.callees o)
      (FinOut Ctx St W SP R o al ah xl xh ·) := by
  generalize hv : (if (xl ||| xh == 0) = true then al else xl) = v
  refine Pc.seq (Q := fun m₀ s => (FinIn Ctx St W SP R al ah xl xh s ∧ s.mem = m₀) ∧ s.gpr .eax = xl ∧
      s.gpr .ecx = al ∧ s.zf = some (xl ||| xh == 0))
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  · have he := h.env
    have h1 := h.xl; have h2 := h.al; have h3 := h.xh
    rw [slotv_eq] at h1 h2 h3
    refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn', h1, h2, h3], ⟨h.keep (by regs []) (by regs [])
      (by regs []) (by mems []) (by mems []) (by mems []), by mems []; exact hm⟩, by regs [], by regs [], by mems []⟩
  refine Pc.seq (Q := fun m₀ s => (FinIn Ctx St W SP R al ah xl xh s ∧ s.mem = m₀) ∧ s.gpr .eax = v) ?_ ?_
  · refine Pc.ite (xl ||| xh == 0) (fun _ _ h => h.2.2.2) (fun ht => ?_) (fun hf => ?_)
    · refine Pc.taint [] (fun m₀ s ⟨⟨h, hm⟩, _, hc, _⟩ => WP.of_runBlock ⟨_, by xrun [], ⟨h.keep (by regs [])
        (by regs []) (by regs []) (by mems []) (by mems []) (by mems []), by mems []; exact hm⟩, by
          rw [← hv, ht]; regs [hc]; rfl⟩) (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    · exact Pc.mono Pc.nil (fun _ _ h => h) fun _ _ ⟨h, ha, _, _⟩ => ⟨h, by rw [← hv, hf]; exact ha⟩
  refine Pc.seq (Q := fun m₀ s => FinIn Ctx St W SP R al ah xl xh s ∧
      slotv s.mem W bO = BitVec.ofNat 32 (v.toNat % 16) ∧ Frame [⟨w64 W + BitVec.ofNat 64 bO, 4⟩] m₀ s.mem)
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨h, hm⟩, ha⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.env.ebp, h₂.1.1.env.ebp]) (by taint_decide)) ?_
  · have he := h.env
    have hand := and15 v
    refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn, ha], ?_⟩
    have fb : Frame [⟨w64 W + BitVec.ofNat 64 bO, 4⟩] s.mem
        (s.mem.writeW (w64 W + BitVec.ofNat 64 bO) (v &&& BitVec.ofNat 32 15)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have sK : ∀ {q}, 128 ≤ q → q + 4 ≤ 240 → slotv (s.mem.writeW (w64 W + BitVec.ofNat 64 bO)
        (v &&& BitVec.ofNat 32 15)) W q = slotv s.mem W q := fun h₁ h₂ =>
      slot_frame fb fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by simp only [bO]; omega)) (by omega) (by decide)
    refine ⟨⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by
        simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact sK (by decide) (by decide)),
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sK (by decide) (by decide)]; exact h.al,
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sK (by decide) (by decide)]; exact h.ah,
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sK (by decide) (by decide)]; exact h.xl,
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sK (by decide) (by decide)]; exact h.xh,
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact ⟨(sK (q := 148) (by decide) (by decide)).trans
        h.rounds.1, h.rounds.2⟩⟩, ?_, ?_⟩
    · simp only [mem_setMem, mem_setReg, mem_arithFlags, slotv_eq, Mem.readW_writeW_self32]; exact hand
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [← hm]; exact fb
  refine Pc.seq (Pc.lift (flush_pc L (yo := 16) (.inr rfl) (b := v.toNat % 16) (Nat.mod_lt _ (by decide)))
    (fun _ s => s.mem) fun m₀ s h => ⟨⟨h.1.env, h.2.1⟩, rfl⟩) ?_
  refine Pc.mono (Pc.lift (tag_pc L (al := alO) (ah := ahO) (tl := xlO) (th := xhO) ho
      (.inr (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)) (alo := al) (ahi := ah) (tlo := xl) (thi := xh))
    (fun _ s => s.mem) fun m₀ s' ⟨s, ⟨h, _, _⟩, fo, _, _⟩ => ⟨⟨fo.env, ?_, rounds_frame fo.frame (kept_tFrame L)
      h.rounds⟩, rfl⟩) (fun _ _ h => h) fun m₀ s'' ⟨s', ⟨s, ⟨h, hb, fb⟩, fo, _, _⟩, tg, _, _⟩ => ?_
  · refine ⟨tg.env, tg.rounds, ?_, fun iv a c hr hl ht => ?_⟩
    · refine (fb.sub fun r hr => ?_).trans ((t_tagFrame fo.frame).trans tg.frame)
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩
    rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit] at hr
    obtain ⟨hj, ha, -⟩ := hr
    have dS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 bO, 4⟩ : Region)],
        (⟨w64 St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
    have hHs : Hk s.mem Ctx = Hk m₀ Ctx := blockAt_frame fb fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
    have hx := buffered_mod hl ht
    rw [hv] at hx
    have ha₁ : Absorbed s.mem (w64 St + BitVec.ofNat 64 16) (w64 St + BitVec.ofNat 64 32) (Hk s.mem Ctx)
        (ghashInput a c) := by
      rw [hHs]
      exact ha.congr (blockAt_frame fb (dS (by decide))) (bytesAt_frame fb (dS (d := 32)
        (k := (ghashInput a c).length % 16) (by omega)) (by omega))
    have hab := fo.abs _ hx ha₁
    have acc := hab.1
    rw [show ghashInput a c ++ zeros (padLen (ghashInput a c).length) = padded a c from rfl,
      Proof.Gcm.whole_of_mod (Proof.Gcm.length_padded a c), List.take_of_length_le (Nat.le_refl _)] at acc
    have hH' : Hk s'.mem Ctx = Hk s.mem Ctx := blockAt_frame fo.frame (ctx_tFrame L (.inr rfl))
    have hC : ciphOf s'.mem Ctx R = ciphOf m₀ Ctx R := by
      rw [ciph_frame fo.frame (ctx_tFrame' L) h.rounds.2, ciph_frame fb (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide))) h.rounds.2]
    have hJ : blockAt s'.mem (w64 St) = blockAt m₀ (w64 St) := by
      have e₁ := blockAt_frame fo.frame (p := w64 St + BitVec.ofNat 64 0) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
        · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
        · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
        · exact (L.stk_st (by decide)).symm
      have e₂ := blockAt_frame fb (dS (d := 0) (k := 16) (by decide))
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e₁ e₂
      rw [e₁, e₂]
    have hva : val64 al ah = a.length % 2 ^ 64 := by rw [val64_eq, hl, BitVec.toNat_ofNat]
    have hvx : val64 xl xh = c.length := by rw [val64_eq, ht]
    rw [tg.out, hH', hHs, acc, hC, hJ, hj, hva, hvx, lensBlock_mod, hHs, Proof.Gcm.fullTag_eq]
  · have sl : ∀ {q}, 112 ≤ q → q + 4 ≤ 240 → slotv s'.mem W q = slotv s.mem W q := fun h₁ h₂ =>
      slot_frame fo.frame (slot_tFrame L (.inr rfl) h₁ h₂)
    exact ⟨by rw [sl (by decide) (by decide)]; exact h.al, by rw [sl (by decide) (by decide)]; exact h.ah,
      by rw [sl (by decide) (by decide)]; exact h.xl, by rw [sl (by decide) (by decide)]; exact h.xh⟩

end

end VG.Proof.AesGcm.X86
