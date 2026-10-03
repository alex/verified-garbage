import VerifiedGarbage.Proof.Bignum.X86_64.CTR2

/-!
# `vg_rsa_public` on x86-64: the setup is constant time but for `m`

The loads of `m` and the input, the comparison, `-m⁻¹` and the number 1
(`setup_ct`). `-m⁻¹ mod 2⁶⁴` is the same in two runs that agree on `m`
(`minv_unique`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- `-n⁻¹ mod 2⁶⁴` is unique. -/
theorem minv_unique {n : Nat} {a b : BitVec 64} (hn : n % 2 = 1) (ha : (n * a.toNat + 1) % 2 ^ 64 = 0)
    (hb : (n * b.toNat + 1) % 2 ^ 64 = 0) : a = b := by
  have hc : Nat.Coprime (2 ^ 64) n := VG.Proof.Bignum.coprime_pow2 hn 64
  have h : n * a.toNat ≡ n * b.toNat [MOD 2 ^ 64] := by
    have e1 : (n * a.toNat + 1) % 2 ^ 64 = (n * b.toNat + 1) % 2 ^ 64 := by rw [ha, hb]
    exact Nat.ModEq.add_right_cancel' 1 e1
  have := Nat.ModEq.cancel_left_of_coprime (hc : Nat.gcd (2 ^ 64) n = 1) h
  apply BitVec.eq_of_toNat_eq
  rw [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this
  exact this

/-! ## The loads -/

/-- The public data of the setup: the working space, the length `k` of `m`,
`m` (its bytes `nb` at `np`) and the input's pointer `ip`. -/
structure SPub where
  B : Addr
  Z : Nat
  k : Nat
  np : Addr
  ip : Addr
  nb : List Byte

/-- `w` for `p.k` bytes. -/
abbrev SPub.w (p : SPub) : Nat := (p.k + 7) / 8

/-- What the setup keeps: the working space, the header's arguments and the
byte strings. -/
def SH (p : SPub) (s : State) : Prop :=
  Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ slot p.w 8 ≤ p.Z ∧ 9 ≤ p.k ∧ p.k < 2 ^ 31 ∧
    word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧ word s.mem p.B (8 * sN) = p.np ∧
    word s.mem p.B (8 * sIn) = p.ip ∧ Src s p.B p.Z p.np p.nb ∧ p.nb.length = p.k ∧
    Spec.Rsa.os2ip p.nb % 2 = 1 ∧ ∃ xb : List Byte, Src s p.B p.Z p.ip xb ∧ xb.length = p.k

/-- `SH` after code that changes only memory in the working space outside the
header's arguments, and not `rdi`. -/
theorem SH.congr {p : SPub} {s t : State} (h : SH p s) {rs : List (Nat × Nat)} (hf : Frm p.B rs s.mem t.mem)
    (hz : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : SH p t := by
  obtain ⟨hs, hdi, hZ, hk1, hk, hK, hN, hIn, hn, hnl, hodd, xb, hx', hxl⟩ := h
  have hi := InScr.of_frm hf hz
  have hfx := Fixed.of_frm hf hx
  exact ⟨hs.congr k.2.2, (k.gpr hr).trans hdi, hZ, hk1, hk, (hfx sK (by decide)).trans hK,
    (hfx sN (by decide)).trans hN, (hfx sIn (by decide)).trans hIn, hn.congrK hi k, hnl, hodd, xb,
    hx'.congrK hi k, hxl⟩

theorem pins_SH : Pins SH [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]

/-- After the first block: the bases and `w`, and the registers for `m`'s load. -/
def S1 (p : SPub) (s : State) : Prop :=
  SH p s ∧ word s.mem p.B (8 * sW) = BitVec.ofNat 64 p.w ∧
    (∀ j < 8, word s.mem p.B (8 * sArr j) = off p.B (slot p.w j)) ∧
    s.gpr .rsi = p.np ∧ s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .rbx = off p.B (slot p.w aN)

/-- After `m`'s load. -/
def S2 (p : SPub) (s : State) : Prop :=
  SH p s ∧ word s.mem p.B (8 * sW) = BitVec.ofNat 64 p.w ∧
    (∀ j < 8, word s.mem p.B (8 * sArr j) = off p.B (slot p.w j)) ∧
    wv s.mem p.B (slot p.w aN) p.w = Spec.Rsa.os2ip p.nb

/-- Before the input's load. -/
def S3 (p : SPub) (s : State) : Prop :=
  S2 p s ∧ s.gpr .rsi = p.ip ∧ s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .rbx = off p.B (slot p.w aX)

theorem pins_S1 : Pins S1 [.rsi, .rcx, .rbx] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2]

theorem pins_S3 : Pins S3 [.rsi, .rcx, .rbx] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]

theorem hdr_fixed {i : Nat} (hi : 8 * i + 8 ≤ 8 * 16 ∧ 6 ≤ i ∨ 22 ≤ i ∧ i < 32) :
    8 * 22 ≤ 8 * i ∨ (8 * 6 ≤ 8 * i ∧ 8 * i + 8 ≤ 8 * 16) := by omega

theorem arr_fixed (w : Nat) {j : Nat} : 8 * 22 ≤ slot w j ∨ (8 * 6 ≤ slot w j ∧ slot w j + 8 * (w + 2) ≤ 8 * 16) :=
  Or.inl (by unfold slot hdrBytes; omega)

theorem slot0_ge (w : Nat) : 8 * 31 + 8 ≤ slot w 0 ∧ slot w 0 + 8 * (w + 2) ≤ slot w 8 :=
  ⟨hdr_lt_slot w 0 (by decide), slot_le (by decide)⟩

/-- The loads of `m` and the input leak the same in runs that agree on `m`. -/
theorem setupLoad_ct : RelCT isa (Two SH) (seqs loadSteps) (Two S2) := by
  unfold loadSteps
  -- `w`, the bases, and `m`'s registers.
  refine RelCT.seq (two_piece (Ψ := S1) _ pins_SH (by taint_decide) ?_) ?_
  · intro p s h
    have h' := h
    obtain ⟨hs, hdi, hZ, hk1, hk, hK, hN, -⟩ := h'
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    refine WP.mono (setupHead_ok hs hdi hZ (by omega) hK hN) fun t ⟨h12, hcx, hsi, hbx, hW, hb, hf, k⟩ =>
      ⟨h.congr hf (fun r hr => ?_) (fun r hr => ?_) k (by decide), hW, hb, hsi, hcx, hbx⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
  -- `m`.
  refine RelCT.seq (two_piece (Ψ := S2) _ pins_S1 (by taint_decide) ?_) ?_
  · intro p s ⟨h, hW, hb, hsi, hcx, hbx⟩
    have h' := h
    obtain ⟨hs, -, hZ, hk1, hk, -, -, -, hn, hnl, -⟩ := h'
    have := slot_le (w := p.w) (show aN < 8 by decide)
    refine WP.mono (loadArr_ok hs (by decide) hZ hn hnl (by omega) hk hsi hcx hbx) fun t ⟨hv, ha, k⟩ =>
      ⟨h.congr (Frm.of_arrays1 ha (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_) k (by decide),
        by rw [ha.hslot (by decide)]; exact hW, fun j hj => by rw [ha.hslot (by unfold sArr; omega)]; exact hb j hj,
        hv⟩
    · rw [List.mem_singleton.mp hr]; exact this.trans hZ
    · rw [List.mem_singleton.mp hr]; exact arr_fixed _
  -- The input's registers.
  refine RelCT.seq (two_piece (Ψ := S3) _ (fun p s₁ s₂ h₁ h₂ => pins_SH p s₁ s₂ h₁.1 h₂.1) (by taint_decide)
    ?_) ?_
  · intro p s ⟨h, hW, hb, hv⟩
    have h' := h
    obtain ⟨hs, hdi, hZ, hk1, hk, hK, -, hIn, -⟩ := h'
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    refine WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = p.ip ∧
        t.gpr .rcx = BitVec.ofNat 64 p.k ∧ t.gpr .rbx = off p.B (slot p.w aX) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sIn) (by unfold sIn sFn; omega),
        hs.ld (d := 8 * sK) (by unfold sK sFn; omega), hs.ld (d := 8 * sArr aX) (by unfold sArr aX; omega), hIn,
        hK, hb aX (by decide)]) rfl) fun t ⟨⟨hsi, hcx, hbx, hm⟩, k⟩ =>
      ⟨⟨h.congr (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) k (by decide), hm ▸ hW,
        hm ▸ hb, hm ▸ hv⟩, hsi, hcx, hbx⟩
  -- The input.
  refine two_piece (Ψ := S2) _ pins_S3 (by taint_decide) ?_
  rintro p s ⟨⟨h, hW, hb, hv⟩, hsi, hcx, hbx⟩
  have h' : SH p s := h
  obtain ⟨hs, -, hZ, hk1, hk, -, -, -, -, -, -, xb, hx, hxl⟩ := h'
  have hn' := slot_le (w := p.w) (show aN < 8 by decide)
  have hx8 := slot_le (w := p.w) (show aX < 8 by decide)
  have hsep := slot_sep (w := p.w) (show aN ≠ aX by decide)
  have hnw : p.B.toNat + slot p.w 8 ≤ 2 ^ 64 := by have := hs.nowrap; omega
  refine WP.mono (loadArr_ok hs (by decide) hZ hx hxl (by omega) hk hsi hcx hbx) fun t ⟨_, ha, k⟩ =>
    ⟨h.congr (Frm.of_arrays1 ha (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_) k (by decide),
      by rw [ha.hslot (by decide)]; exact hW, fun j hj => by rw [ha.hslot (by unfold sArr; omega)]; exact hb j hj,
      by rw [ha.wv_of_not_mem (by decide) (by decide) hnw]; exact hv⟩
  · rw [List.mem_singleton.mp hr]; exact hx8.trans hZ
  · rw [List.mem_singleton.mp hr]; exact arr_fixed _

/-! ## The comparison, `-m⁻¹` and the number 1 -/

/-- The mask's store, and `-m⁻¹` into the header: the header is whole. -/
theorem blk7_ok {t : State} {B : Addr} {Z w : Nat} (hs : Scr t B Z) (hdi : t.gpr .rdi = B)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hW : word t.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hb : ∀ j < 8, word t.mem B (8 * sArr j) = off B (slot w j))
    (h10 : t.gpr .r10 = off B (slot w aN)) (hodd : (word t.mem B (slot w aN)).toNat % 2 = 1) :
    WP isa (.block (([.store (hdr sMask) .rbp, .mov .rbx (.mem (at0 .r10))] : List Instr) ++ minv ++
        ([.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)] : List Instr))) t fun t' =>
      ∃ mi : BitVec 64, Hdr t'.mem B w mi ∧ Scr t' B Z ∧ t'.gpr .rdi = B ∧
        t'.gpr .rcx = BitVec.ofNat 64 0 ∧ Keep [.rbx, .rax, .rcx, .rdx, .rsi, .r15] t t' := by
  have hn := hs.nowrap
  have h0 := slot_le (w := w) (show 0 < 8 by decide)
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have hsN : ∀ v : BitVec 64, (t.mem.writeW (off B (8 * sMask)) v).readW (off B (slot w aN)) 64 =
      word t.mem B (slot w aN) := fun v =>
    (writeW_outside _ B _ (by unfold sMask sFn; omega)).word
      (by have := hdr_lt_slot w aN (show sMask < 32 by decide); omega)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rbx] (Q := fun t₁ => t₁.gpr .rbx = word t.mem B (slot w aN) ∧
      t₁.mem = t.mem.writeW (off B (8 * sMask)) (t.gpr .rbp)) (by
    xrun [State.ea, hdr, at0, hdi, hdrOff, hs.st (d := 8 * sMask) (by unfold sMask sFn; omega), h10, hsN,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs.ld (d := slot w aN) (by have := slot_le (w := w) (show aN < 8 by decide); omega)]) rfl)
    fun t₃ ⟨⟨hbx₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (minv_ok t₃ (by rw [hbx₃]; exact hodd)) fun t₄ ⟨_, k₄, hm₄⟩ => ?_
  have hs₄ := (hs.congr k₃.2.2).congr k₄.2.2
  have hdi₄ : t₄.gpr .rdi = B := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi)
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t' => t'.gpr .rcx = BitVec.ofNat 64 0 ∧
      t'.mem = t₄.mem.writeW (off B (8 * sMinv)) (t₄.gpr .r15)) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.st (d := 8 * sMinv) (by unfold sMinv; omega)]) rfl)
    fun t₅ ⟨⟨hcx₅, hm₅⟩, k₅⟩ => ⟨t₄.gpr .r15, ?_, hs₄.congr k₅.2.2, (k₅.gpr (by decide)).trans hdi₄, hcx₅,
      ((k₃.trans k₄).trans k₅).mono (by decide)⟩
  have hm₅' : t₅.mem = (t.mem.writeW (off B (8 * sMask)) (t.gpr .rbp)).writeW (off B (8 * sMinv))
      (t₄.gpr .r15) := by rw [hm₅, hm₄, hm₃]
  have hhd : ∀ i < 32, i ≠ sMask → i ≠ sMinv → word t₅.mem B (8 * i) = word t.mem B (8 * i) :=
    fun i hi h1 h2 => by
      rw [hm₅', hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h1)]
  exact ⟨by rw [hhd sW (by decide) (by decide) (by decide)]; exact hW, by rw [hm₅', word_writeW_self],
    fun j hj => by rw [hhd (sArr j) (by unfold sArr; omega) (by unfold sArr sMask sFn; omega)
      (by unfold sArr sMinv; omega)]; exact hb j hj⟩

/-- The public data of the comparison, `-m⁻¹` and the number 1: the working
space and `w`. -/
structure RPub where
  B : Addr
  Z : Nat
  w : Nat

/-- What the comparison, `-m⁻¹` and the number 1 need: the working space, the
header's `w` and bases, and `m` odd. -/
def SR (p : RPub) (s : State) : Prop :=
  Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ slot p.w 8 ≤ p.Z ∧ 2 ≤ p.w ∧ p.w < 2 ^ 31 ∧
    word s.mem p.B (8 * sW) = BitVec.ofNat 64 p.w ∧ (∀ j < 8, word s.mem p.B (8 * sArr j) = off p.B (slot p.w j)) ∧
    (word s.mem p.B (slot p.w aN)).toNat % 2 = 1

/-- `SR` with the same memory, and `rdi` kept. -/
theorem SR.mem {p : RPub} {s t : State} (h : SR p s) (hm : t.mem = s.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs) : SR p t :=
  let ⟨hs, hdi, hZ, hw, hw', hW, hb, hodd⟩ := h
  ⟨hs.congr k.2.2, (k.gpr hr).trans hdi, hZ, hw, hw', hm ▸ hW, hm ▸ hb, hm ▸ hodd⟩

/-- After the comparison's registers. -/
def S5 (p : RPub) (s : State) : Prop :=
  SR p s ∧ s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .rbx = off p.B (slot p.w aX) ∧
    s.gpr .r10 = off p.B (slot p.w aN) ∧ s.gpr .rbp = mask false

/-- After the comparison. -/
def S6 (p : RPub) (s : State) : Prop :=
  SR p s ∧ s.gpr .r10 = off p.B (slot p.w aN) ∧ s.gpr .r12 = BitVec.ofNat 64 p.w

/-- After `-m⁻¹`. -/
def S7 (p : RPub) (s : State) : Prop :=
  ∃ mi : BitVec 64, Hdr s.mem p.B p.w mi ∧ Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ slot p.w 8 ≤ p.Z ∧
    s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .rcx = BitVec.ofNat 64 0

theorem SH.k1 {p : SPub} {s : State} (h : SH p s) : 2 ≤ p.w := by have := h.2.2.2.1; unfold SPub.w; omega

/-- `S2` gives what the comparison, `-m⁻¹` and the number 1 need. -/
theorem S2.sr {p : SPub} {s : State} (h : S2 p s) : SR ⟨p.B, p.Z, p.w⟩ s := by
  obtain ⟨h, hW, hb, hv⟩ := h
  have hk := h.k1
  obtain ⟨hs, hdi, hZ, -, hk', -, -, -, -, -, hodd, -⟩ := h
  refine ⟨hs, hdi, hZ, hk, show p.w < 2 ^ 31 by unfold SPub.w; omega, hW, hb, ?_⟩
  rw [← wv_mod64 _ _ _ (show 1 ≤ p.w by omega), Nat.mod_mod_of_dvd _ (by decide), hv, hodd]

/-- The comparison, `-m⁻¹` and the number 1 leak the same in runs that agree
on `m`. -/
theorem setupRest_ct : RelCT isa (Two SR) (seqs restSteps) fun _ _ => True := by
  unfold restSteps
  -- The comparison's registers.
  refine RelCT.seq (two_piece (Ψ := S5) [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · intro p s h
    have h' := h
    obtain ⟨hs, hdi, hZ, -, -, hW, hb, -⟩ := h'
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    refine WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧
        t.gpr .rbx = off p.B (slot p.w aX) ∧ t.gpr .r10 = off p.B (slot p.w aN) ∧ t.gpr .rbp = mask false ∧
        t.mem = s.mem) (by
      xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sW) (by unfold sW; omega),
        hs.ld (d := 8 * sArr aX) (by unfold sArr aX; omega), hs.ld (d := 8 * sArr aN) (by unfold sArr aN; omega),
        hW, hb aX (by decide), hb aN (by decide)]) rfl) fun t ⟨⟨h12, hbx, h10, hbp, hm⟩, k⟩ =>
      ⟨h.mem hm k (by decide), h12, hbx, h10, hbp⟩
  -- The comparison.
  refine RelCT.seq (two_piece (Ψ := S6) [.rbx, .r10, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · intro p s ⟨h, h12, hbx, h10, hbp⟩
    have h' := h
    obtain ⟨hs, -, hZ, hk, hk', -⟩ := h'
    refine WP.mono (cmpLoop_ok hs hbx h10 h12 hbp (by omega) hk'
      (by have := slot_le (w := p.w) (show aX < 8 by decide); omega)
      (by have := slot_le (w := p.w) (show aN < 8 by decide); omega)) fun t ⟨_, hm, k⟩ =>
      ⟨h.mem hm k (by decide), (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12⟩
  -- `-m⁻¹`, and the number 1.
  refine RelCT.seq (two_piece (Ψ := S7) [.rdi, .r10] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.2.1, h₂.1.2.1]
    · rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · intro p s ⟨h, h10, h12⟩
    obtain ⟨hs, hdi, hZ, hk, -, hW, hb, hodd₀⟩ := h
    exact WP.mono (blk7_ok hs hdi hZ (by omega) hW hb h10 hodd₀) fun t ⟨mi, hH, hs', hdi', hcx, k⟩ =>
      ⟨mi, hH, hs', hdi', hZ, (k.gpr (by decide)).trans h12, hcx⟩
  -- The number 1.
  rw [setWord_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => S7 p s ∧ s.gpr .r8 = off p.B (slot p.w aOne)) [.rdi]
    (fun p s₁ s₂ ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide) ?_)
    (two_taint [.r8, .r12, .rcx] (fun p s₁ s₂ h₁ h₂ r hr => by
      obtain ⟨⟨_, _, _, _, _, a₁, b₁⟩, c₁⟩ := h₁
      obtain ⟨⟨_, _, _, _, _, a₂, b₂⟩, c₂⟩ := h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [c₁, c₂]
      · rw [a₁, a₂]
      · rw [b₁, b₂]) (by taint_decide))
  rintro p s ⟨mi, hH, hs, hdi, hZ, h12, hcx⟩
  have hl : InRegions (s.rd ++ s.wr) (off p.B (8 * sArr aOne)) 8 :=
    hs.ld (by have := hdr_lt_slot p.w 8 (show sArr aOne < 32 by decide); omega)
  refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off p.B (slot p.w aOne) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl, hH.harr aOne (by decide)]) rfl)
    fun t ⟨⟨h8, hm⟩, k⟩ => ⟨⟨mi, hm ▸ hH, hs.congr k.2.2, (k.gpr (by decide)).trans hdi, hZ,
      (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hcx⟩, h8⟩

end VG.Proof.Bignum.X86_64
