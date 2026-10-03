import VerifiedGarbage.Proof.Bignum.X86_64.PcCode
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain

/-!
# `vg_rsa_public_precompute` on x86-64: constant time but for `n`

Every piece's addresses and branches depend only on the pointers, the
lengths and `n`: the load of `m` and `-m⁻¹` (`pcLoad_ct`), `R² mod m`
(`r2_ct`), the copies to `pre` (`pcOut_ct`), and the whole function
(`pcCode_constantTime`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-! ## `main` -/

/-- The public data of `main`: the working space, `k`, `pre`, and `m` (its
bytes `nb` at `np`). -/
structure PcPub where
  B : Addr
  Z : Nat
  k : Nat
  op : Addr
  np : Addr
  nb : List Byte

abbrev PcPub.w (p : PcPub) : Nat := (p.k + 7) / 8
abbrev PcPub.N (p : PcPub) : Nat := Spec.Rsa.os2ip p.nb

/-- `pcMain_ok`'s hypotheses. -/
def PcM (p : PcPub) (s : State) : Prop :=
  Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    word s.mem p.B (8 * sOut) = p.op ∧ word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    word s.mem p.B (8 * sN) = p.np ∧ Src s p.B p.Z p.np p.nb ∧ p.nb.length = p.k ∧
    Spec.Rsa.modulusValid p.N p.k = true ∧ (∀ i < 2 * p.w, InRegions s.wr (off p.op (8 * i)) 8) ∧
    (∀ i < 16 * p.w, p.Z ≤ ofs p.B (p.op + BitVec.ofNat 64 i))

/-- `PcM` after code that changes only memory in the working space outside
the header's arguments, and not `rdi`. -/
theorem PcM.congr {p : PcPub} {s t : State} (h : PcM p s) {rs : List (Nat × Nat)}
    (hf : Frm p.B rs s.mem t.mem) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z)
    (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : PcM p t := by
  obtain ⟨hs, hdi, hZ, hk1, hk2, hO, hK, hN, hn, hnl, hv, hpw, hps⟩ := h
  have hi := InScr.of_frm hf hz
  have hfx := Fixed.of_frm hf hx
  exact ⟨hs.congr k.2.2, (k.gpr hr).trans hdi, hZ, hk1, hk2, (hfx sOut (by decide)).trans hO,
    (hfx sK (by decide)).trans hK, (hfx sN (by decide)).trans hN, hn.congrK hi k, hnl, hv,
    fun i hi => by rw [k.2.2]; exact hpw i hi, hps⟩

theorem pins_PcM : Pins PcM [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]

/-- After the first block. -/
def Pc1 (p : PcPub) (s : State) : Prop :=
  PcM p s ∧ word s.mem p.B (8 * sW) = BitVec.ofNat 64 p.w ∧
    (∀ j < 8, word s.mem p.B (8 * sArr j) = off p.B (slot p.w j)) ∧
    s.gpr .rsi = p.np ∧ s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .rbx = off p.B (slot p.w aN)

/-- After `m`'s load. -/
def Pc2 (p : PcPub) (s : State) : Prop :=
  PcM p s ∧ word s.mem p.B (8 * sW) = BitVec.ofNat 64 p.w ∧
    (∀ j < 8, word s.mem p.B (8 * sArr j) = off p.B (slot p.w j)) ∧
    wv s.mem p.B (slot p.w aN) p.w = p.N ∧ s.gpr .rbx = off p.B (slot p.w aN)

/-- After `-m⁻¹`: `R² mod m`'s hypotheses, and `PcM`. -/
def Pc3 (p : PcPub) (s : State) : Prop :=
  ∃ mi : BitVec 64, PcM p s ∧ R2Pre ⟨⟨p.B, p.Z, p.w, mi⟩, p.N⟩ s

theorem pins_Pc1 : Pins Pc1 [.rdi, .rsi, .rcx, .rbx] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.1.2.1, h₂.1.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2]

theorem pins_Pc2 : Pins Pc2 [.rdi, .rbx] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.1.2.1, h₂.1.2.1]
  · rw [h₁.2.2.2.2, h₂.2.2.2.2]

/-- The load of `m` and `-m⁻¹` leak the same in runs that agree on `m`. -/
theorem pcLoad_ct : RelCT isa (Two PcM) (seqs pcLoad) (Two Pc3) := by
  unfold pcLoad
  -- `w`, the bases, and `m`'s registers.
  refine RelCT.seq (two_piece (Ψ := Pc1) _ pins_PcM (by taint_decide) ?_) ?_
  · intro p s h
    have h' := h
    obtain ⟨hs, hdi, hZ, hk1, hk2, -, hK, hN, -⟩ := h'
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    refine WP.mono (setupHead_ok hs hdi hZ (by omega) hK hN) fun t ⟨_, hcx, hsi, hbx, hW, hb, hf, k⟩ =>
      ⟨h.congr hf (fun r hr => ?_) (fun r hr => ?_) k (by decide), hW, hb, hsi, hcx, hbx⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
  -- `m`.
  refine RelCT.seq (two_piece (Ψ := Pc2) _ pins_Pc1 (by taint_decide) ?_) ?_
  · intro p s ⟨h, hW, hb, hsi, hcx, hbx⟩
    have h' := h
    obtain ⟨hs, -, hZ, hk1, hk2, -, -, -, hn, hnl, -⟩ := h'
    have := slot_le (w := p.w) (show aN < 8 by decide)
    refine WP.mono (loadArr_ok hs (by decide) hZ hn hnl (by omega) (by omega) hsi hcx hbx) fun t ⟨hv, ha, k⟩ =>
      ⟨h.congr (Frm.of_arrays1 ha (List.mem_singleton_self _)) (fun r hr => ?_) (fun r hr => ?_) k (by decide),
        by rw [ha.hslot (by decide)]; exact hW, fun j hj => by rw [ha.hslot (by unfold sArr; omega)]; exact hb j hj,
        hv, (k.gpr (by decide)).trans hbx⟩
    · rw [List.mem_singleton.mp hr]; exact this.trans hZ
    · rw [List.mem_singleton.mp hr]; exact arr_fixed _
  -- `-m⁻¹`.
  refine two_piece (Ψ := Pc3) _ pins_Pc2 (by taint_decide) ?_
  intro p s ⟨h, hW, hb, hv, hbx⟩
  have h' := h
  obtain ⟨hs, hdi, hZ, hk1, hk2, -, -, -, -, hnl, hval, -⟩ := h'
  obtain ⟨hodd, -, hlo⟩ := valid_facts hval hk1
  have hn := hs.nowrap
  have h0 := slot_le (w := p.w) (show 0 < 8 by decide)
  have h8 := hdr_lt_slot p.w 0 (show 31 < 32 by decide)
  have hsN := slot_le (w := p.w) (show aN < 8 by decide)
  have hw1 : 2 ≤ p.w := by unfold PcPub.w; omega
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eAN : sArr aN = 8 := rfl
  have hZ8 : 8 * 32 ≤ p.Z := by omega
  have hodd₀ : (word s.mem p.B (slot p.w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ (show 1 ≤ p.w by omega), Nat.mod_mod_of_dvd _ (by decide), hv, hodd]
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  rw [seqs_one, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r10, .r12, .rbx] (Q := fun t => t.gpr .r10 = off p.B (slot p.w aN) ∧
      t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .rbx = word s.mem p.B (slot p.w aN) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, at0, hdi, hdrOff, hl sW (by decide), hbx, hW,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hs.ld (d := slot p.w aN) (by omega)])
    rfl) fun t₃ ⟨⟨h10₃, h12₃, hbx₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (minv_ok t₃ (by rw [hbx₃]; exact hodd₀)) fun t₄ ⟨hinv, k₄, hm₄⟩ => ?_
  rw [hbx₃] at hinv
  have hs₄ := (hs.congr k₃.2.2).congr k₄.2.2
  have hdi₄ : t₄.gpr .rdi = p.B := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₄.mem.writeW (off p.B (8 * sMinv)) (t₄.gpr .r15)) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.st (d := 8 * sMinv) (by unfold sMinv; omega)]) rfl)
    fun t ⟨hm, k₅⟩ => ?_
  have hm' : t.mem = s.mem.writeW (off p.B (8 * sMinv)) (t₄.gpr .r15) := by rw [hm, hm₄, hm₃]
  have hwo : Outside p.B (8 * sMinv) 8 s.mem t.mem := by rw [hm']; exact writeW_outside _ p.B _ (by omega)
  have kk := (k₃.trans k₄).trans k₅
  refine ⟨t₄.gpr .r15, h.congr (Frm.of_outside hwo (List.mem_singleton_self _)) (by simp [sMinv]; omega)
    (by simp [sMinv]) kk (by decide), ⟨⟨hs₄.congr k₅.2.2, (k₅.gpr (by decide)).trans hdi₄, ⟨?_, ?_, fun j hj => ?_⟩⟩, hZ⟩,
    hw1, by dsimp only; unfold PcPub.w; omega, ?_, ?_, (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h12₃),
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans h10₃), hodd, hlo⟩
  · rw [hwo.word (by unfold sW sMinv; omega) (by omega)]; exact hW
  · rw [hm', word_writeW_self]
  · rw [hwo.word (d := 8 * sArr j) (by unfold sArr sMinv; omega) (by unfold sArr; omega)]; exact hb j hj
  · dsimp only
    rw [hwo.wv (by have := hdr_lt_slot p.w aN (show sMinv < 32 by decide); omega) (by omega)]; exact hv
  · dsimp only
    rw [hwo.word (by have := hdr_lt_slot p.w aN (show sMinv < 32 by decide); omega) (by omega)]; exact hinv

/-! ## `R² mod m` -/

/-- `main`'s public data with `-m⁻¹`. -/
abbrev PcPub.L (q : PcPub × BitVec 64) : Lay := ⟨q.1.B, q.1.Z, q.1.w, q.2⟩

/-- `-m⁻¹` is the same in runs that agree on `m`. -/
theorem pc3_minv {p : PcPub} {s₁ s₂ : State} {mi₁ mi₂ : BitVec 64}
    (h₁ : R2Pre ⟨⟨p.B, p.Z, p.w, mi₁⟩, p.N⟩ s₁) (h₂ : R2Pre ⟨⟨p.B, p.Z, p.w, mi₂⟩, p.N⟩ s₂) : mi₁ = mi₂ := by
  have e : ∀ {s : State} {mi : BitVec 64}, R2Pre ⟨⟨p.B, p.Z, p.w, mi⟩, p.N⟩ s →
      ((p.N % 2 ^ 64) * mi.toNat + 1) % 2 ^ 64 = 0 := fun h => by
    have hw := h.2.1
    have hv := h.2.2.2.1
    have hi := h.2.2.2.2.1
    dsimp only at hw hv hi
    rwa [← wv_mod64 _ _ _ (show 1 ≤ p.w by omega), hv] at hi
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h₁.2.2.2.2.2.2.2.1) (e h₁) (e h₂)

/-- What the copies to `pre` need. -/
def PcO (q : PcPub × BitVec 64) (s : State) : Prop :=
  GoodL (PcPub.L q) s ∧ 2 ≤ q.1.w ∧ q.1.w < 2 ^ 30 ∧ word s.mem q.1.B (8 * sOut) = q.1.op ∧
    (∀ i < 2 * q.1.w, InRegions s.wr (off q.1.op (8 * i)) 8) ∧
    (∀ i < 16 * q.1.w, q.1.Z ≤ ofs q.1.B (q.1.op + BitVec.ofNat 64 i))

/-- `R² mod m` leaks the same in runs that agree on `m`. -/
theorem pcR2_ct (M : Mont) : RelCT isa (Two Pc3) (seqs (r2Steps M)) (Two PcO) := by
  have h := two_post (Φ := fun (q : PcPub × BitVec 64) s => PcM q.1 s ∧ R2Pre ⟨PcPub.L q, q.1.N⟩ s)
    (Ψ := PcO) (two_map (fun q => (⟨PcPub.L q, q.1.N⟩ : R2Pub)) (fun _ _ h => h.2) (r2_ct M)) ?_
  · exact h.mono (fun _ _ hp => two_bind (fun p s₁ s₂ ⟨mi₁, m₁, r₁⟩ ⟨mi₂, m₂, r₂⟩ => by
      obtain rfl := pc3_minv r₁ r₂
      exact ⟨(p, mi₁), ⟨m₁, r₁⟩, m₂, r₂⟩) hp) fun _ _ h => h
  rintro ⟨p, mi⟩ s ⟨hm, hr⟩
  obtain ⟨hg, hw, hw', hn, hinv, h12, h10, hodd, hlo⟩ := hr
  dsimp only at hg hw hw' hn hinv h12 h10 hodd hlo
  refine WP.mono (r2_ok M hg.1 hg.2 hw hw' hn hinv h12 h10 hodd hlo) fun t ⟨hg', _, _, f, k⟩ =>
    ⟨⟨hg', hg.2⟩, hw, hw', ?_, fun i hi => by rw [k.2.2]; exact hm.2.2.2.2.2.2.2.2.2.2.2.1 i hi,
      hm.2.2.2.2.2.2.2.2.2.2.2.2⟩
  rw [(Fixed.of_frm f (r2Ranges_fixed _)) sOut (by decide)]
  exact hm.2.2.2.2.2.1

/-! ## The copies to `pre` -/

/-- `Good` after code that changes only memory outside the working space. -/
theorem Good.of_inScr {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hi : ∀ x, ofs B x < Z → t.mem x = s.mem x) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = B) : Good t B Z w minv := by
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := w) (show 0 < 8 by decide)
  have hw : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    Mem.readW_congr fun b hb => hi _ (by rw [ofs_off B (d := 8 * i) (i := b) (by omega)]; omega)
  exact ⟨hg.scr.congr hwr, hdi, ⟨by rw [hw sW (by decide)]; exact hg.hdr.hw,
    by rw [hw sMinv (by decide)]; exact hg.hdr.hminv,
    fun j hj => by rw [hw (sArr j) (by unfold sArr; omega)]; exact hg.hdr.harr j hj⟩⟩

/-- Before the first copy. -/
def PcO1 (q : PcPub × BitVec 64) (s : State) : Prop :=
  PcO q s ∧ s.gpr .r12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .rsi = off q.1.B (slot q.1.w aN) ∧
    s.gpr .rbx = off q.1.op 0

/-- After the first copy. -/
def PcO2 (q : PcPub × BitVec 64) (s : State) : Prop :=
  PcO q s ∧ s.gpr .r12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .rbx = off q.1.op 0

/-- Before the second copy. -/
def PcO3 (q : PcPub × BitVec 64) (s : State) : Prop :=
  PcO q s ∧ s.gpr .r12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .rsi = off q.1.B (slot q.1.w aR2) ∧
    s.gpr .rbx = off q.1.op (8 * q.1.w)

theorem pins_PcO : Pins PcO [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.rdi, h₂.1.1.rdi]

/-- A copy of `w` words from the working space to `pre` at `pre + 8 d`,
`d ≤ w`: the working space is as it was. -/
theorem pcCopy_ok {q : PcPub × BitVec 64} {s : State} (h : PcO q s) {e d : Nat} (hd : d ≤ q.1.w)
    (he : e + 8 * q.1.w ≤ q.1.Z) (hsi : s.gpr .rsi = off q.1.B e) (hbx : s.gpr .rbx = off q.1.op (8 * d))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 q.1.w) :
    WP isa copyWords s fun t => PcO q t ∧ Keep [.rax, .r14] s t := by
  obtain ⟨hg, hw, hw', hO, hpw, hps⟩ := h
  have hs : Scr s q.1.B q.1.Z := hg.1.scr
  have hn := hs.nowrap
  have hZ : slot q.1.w 8 ≤ q.1.Z := hg.2
  have hsep : ∀ x, ofs q.1.B x < q.1.Z → 16 * q.1.w ≤ ofs q.1.op x := fun x hx => le_ofs_of_sep hps hx
  refine WP.mono (copyWords_ok hsi hbx h12 (by omega) (by omega) (by omega)
    (fun j hj => hs.ld (by omega))
    (fun j hj => by rw [show 8 * d + 8 * j = 8 * (d + j) by omega]; exact hpw (d + j) (by omega))
    (fun j hj b hb => Or.inr (le_trans (by omega)
      (hsep _ (by rw [ofs_off q.1.B (d := e + 8 * j) (i := b) (by omega)]; omega)))))
    fun t ⟨_, _, ho, k⟩ => ?_
  have hi : ∀ x, ofs q.1.B x < q.1.Z → t.mem x = s.mem x := fun x hx =>
    ho x (Or.inr (by have := hsep x hx; omega))
  refine ⟨⟨⟨Good.of_inScr (hg.1 : Good s q.1.B q.1.Z q.1.w q.2) hZ hi k.2.2
    ((k.gpr (by decide)).trans hg.1.rdi), hZ⟩, hw, hw', ?_,
    fun i hi' => by rw [k.2.2]; exact hpw i hi', hps⟩, k⟩
  rw [← hO]
  exact Mem.readW_congr fun b hb => hi _ (by
    have := hdr_lt_slot q.1.w 0 (show 31 < 32 by decide)
    have := slot_le (w := q.1.w) (show 0 < 8 by decide)
    rw [ofs_off q.1.B (d := 8 * sOut) (i := b) (by unfold sOut sFn; omega)]; unfold sOut sFn; omega)

theorem PcO.mem {q : PcPub × BitVec 64} {s t : State} (h : PcO q s) (hm : t.mem = s.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : PcO q t := by
  obtain ⟨hg, hw, hw', hO, hpw, hps⟩ := h
  exact ⟨⟨Good.of_inScr (hg.1 : Good s q.1.B q.1.Z q.1.w q.2) hg.2 (fun x _ => by rw [hm]) k.2.2
    ((k.gpr hr).trans hg.1.rdi), hg.2⟩, hw, hw', by rw [hm]; exact hO,
    fun i hi => by rw [k.2.2]; exact hpw i hi, hps⟩

/-- The copies to `pre` leak the same in runs with the same working space and
`pre`. -/
theorem pcOut_ct : RelCT isa (Two PcO) (seqs pcOut) fun _ _ => True := by
  unfold pcOut
  -- The first copy's registers.
  refine RelCT.seq (two_piece (Ψ := PcO1) _ pins_PcO (by taint_decide) ?_) ?_
  · intro q s h
    have hs : Scr s q.1.B q.1.Z := h.1.1.scr
    have hn := hs.nowrap
    have hZ : slot q.1.w 8 ≤ q.1.Z := h.1.2
    obtain ⟨g0, g8⟩ := slot0_ge q.1.w
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off q.1.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
    refine WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 q.1.w ∧
        t.gpr .rsi = off q.1.B (slot q.1.w aN) ∧ t.gpr .rbx = off q.1.op 0 ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, h.1.1.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hl sOut (by decide),
        h.1.1.hdr.hw, h.1.1.hdr.harr aN (by decide), h.2.2.2.1]) rfl)
      fun t ⟨⟨h12, hsi, hbx, hm⟩, k⟩ => ⟨h.mem hm k (by decide), h12, hsi, hbx⟩
  -- The first copy.
  refine RelCT.seq (two_piece (Ψ := PcO2) [.rsi, .rbx, .r12] (fun q s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · rintro q s ⟨h, h12, hsi, hbx⟩
    have := slot_le (w := q.1.w) (show aN < 8 by decide)
    have hZ : slot q.1.w 8 ≤ q.1.Z := h.1.2
    exact WP.mono (pcCopy_ok h (d := 0) (by omega) (by omega) hsi (by rw [hbx]) h12)
      fun t ⟨h', k⟩ => ⟨h', (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hbx⟩
  -- The second copy's registers.
  refine RelCT.seq (two_piece (Ψ := PcO3) [.rdi, .r12, .rbx] (fun q s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1.1.1.rdi, h₂.1.1.1.rdi]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]) (by taint_decide) ?_) ?_
  · rintro q s ⟨h, h12, hbx⟩
    have hs : Scr s q.1.B q.1.Z := h.1.1.scr
    have hn := hs.nowrap
    have hZ : slot q.1.w 8 ≤ q.1.Z := h.1.2
    obtain ⟨g0, g8⟩ := slot0_ge q.1.w
    have hax8 : ∀ r : BitVec 64, r = BitVec.ofNat 64 q.1.w → r + r + (r + r) + (r + r + (r + r)) =
        BitVec.ofNat 64 (8 * q.1.w) := by
      rintro r rfl; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega
    have hbx' : s.gpr .rbx = q.1.op := by rw [hbx]; simp [off]
    refine WP.mono (WP.keep [.rax, .rbx, .rsi] (Q := fun t => t.gpr .rbx = off q.1.op (8 * q.1.w) ∧
        t.gpr .rsi = off q.1.B (slot q.1.w aR2) ∧ t.mem = s.mem) (by
      unfold eightW
      simp only [List.cons_append, List.nil_append]
      xrun [State.ea, hdr, h.1.1.rdi, hdrOff, hs.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega),
        h.1.1.hdr.harr aR2 (by decide), h12, hbx', hax8 _ rfl]) rfl)
      fun t ⟨⟨hbx₁, hsi, hm⟩, k⟩ => ⟨h.mem hm k (by decide), (k.gpr (by decide)).trans h12, hsi, hbx₁⟩
  -- The second copy and the exit.
  exact two_taint [.rsi, .rbx, .r12, .rdi] (fun q s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.1.1.1.rdi, h₂.1.1.1.rdi]) (by taint_decide)

/-- `main` leaks the same in runs that agree on the public data and `n`. -/
theorem pcMain_ct (M : Mont) : RelCT isa (Two PcM) (Precompute.main M.mm) fun _ _ => True := by
  rw [pcMain_eq M]
  refine RelCT.seqs_append (by simp [pcLoad]) (by simp [r2Steps]) (RelCT.seq pcLoad_ct ?_)
  exact RelCT.seqs_append (by simp [r2Steps]) (by simp [pcOut]) (RelCT.seq (pcR2_ct M) pcOut_ct)

/-! ## The whole function -/

/-- A state the contract allows, with the public data `p`. -/
def PcC (p : PcPub) (s : State) : Prop :=
  pcContract.pre s ∧ s.gpr .r8 = p.B ∧ (s.gpr .r9).toNat * 8 = p.Z ∧ (s.gpr .rcx).toNat = p.k ∧
    s.gpr .rdi = p.op ∧ s.gpr .rdx = p.np ∧ Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = p.nb

/-- After the entry and the modulus' check. -/
def PcC3 (p : PcPub) (t : State) : Prop :=
  Scr t p.B p.Z ∧ t.gpr .rdi = p.B ∧ slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    word t.mem p.B (8 * sOut) = p.op ∧ word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    word t.mem p.B (8 * sN) = p.np ∧ Src t p.B p.Z p.np p.nb ∧ p.nb.length = p.k ∧
    (∀ i < 2 * p.w, InRegions t.wr (off p.op (8 * i)) 8) ∧
    (∀ j < 16 * p.w, InRegions t.wr (p.op + BitVec.ofNat 64 j) 1) ∧
    (∀ i < 16 * p.w, p.Z ≤ ofs p.B (p.op + BitVec.ofNat 64 i)) ∧
    t.zf = some (Spec.Rsa.modulusValid p.N p.k)

/-- `vg_rsa_public_precompute` leaks the same in runs that agree on the public
data and `n`. -/
theorem pcCode_ct (M : Mont) : RelCT isa (Two PcC) (Precompute.code M.mm) fun _ _ => True := by
  unfold Precompute.code
  refine RelCT.seq (two_piece (Ψ := PcC3) [.r8, .rdx, .rcx] (fun p s₁ s₂ h₁ h₂ r hr => by
    obtain ⟨-, a₁, -, c₁, -, d₁, -⟩ := h₁
    obtain ⟨-, a₂, -, c₂, -, d₂, -⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [d₁, d₂]
    · rw [← ofNat_toNat64 (s₁.gpr .rcx), ← ofNat_toNat64 (s₂.gpr .rcx), c₁, c₂]) (by taint_decide) ?_) ?_
  · rintro ⟨B, Z, k, op, np, nb⟩ s ⟨hs, hB, hZ, hk, hop, hnp, hnb⟩
    have c := pcCtx_of hs
    have hZ' := c.hZ
    have hk1 := c.hk1
    have hk2 := c.hk2
    have hn := c.hs.nowrap
    rw [WP.block_append_iff]
    refine WP.mono (pcEntry_ok rfl fun i hi => c.hs.st (by omega))
      fun t₁ ⟨hdi, _, _, _, _, _, _, hO, hN, hK, ho₁, k₁⟩ => ?_
    have i₁ : InScr (s.gpr .r8) ((s.gpr .r9).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega)
    have hnb₁ := c.hnb.congrK i₁ k₁
    refine WP.mono (invalid_ok ((k₁.gpr (by decide)).trans rfl) (by rw [k₁.gpr (by decide), ofNat_toNat64])
      hk1 hk2 (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi))
      (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
    have kk := k₁.trans k₂
    subst hB hZ hk hop hnp hnb
    exact ⟨c.hs.congr kk.2.2, (k₂.gpr (by decide)).trans hdi,
      show slot (((s.gpr .rcx).toNat + 7) / 8) 8 ≤ (s.gpr .r9).toNat * 8 by unfold slot hdrBytes; omega, hk1, hk2,
      by rw [hm₂]; exact hO, by rw [hm₂, hK, ofNat_toNat64], by rw [hm₂]; exact hN,
      c.hnb.congrK (by rw [hm₂]; exact i₁) kk, bytesAt_length _ _ _,
      fun i hi => by rw [kk.2.2]; exact c.hpw i hi, fun j hj => by rw [kk.2.2]; exact c.hpb j hj, c.hps, hz₂⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, z₁⟩ := h₁
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, z₂⟩ := h₂
    simp only [eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    unfold Precompute.fail
    have pin : ∀ p t, (PcC3 p t ∧ isa.eval .ne t = some true) → t.gpr .rdi = p.B := fun p t h => h.1.2.1
    refine RelCT.seq (two_piece (Ψ := fun p t => t.gpr .rsi = p.op ∧
        t.gpr .rcx = BitVec.ofNat 64 (16 * p.w) ∧ t.gpr .rdi = p.B) [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [pin p s₁ h₁, pin p s₂ h₂]) (by taint_decide) ?_)
      (two_taint [.rsi, .rcx, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    rintro p t ⟨⟨hs, hdi, hZ, hk1, hk2, hO, hK, -⟩, -⟩
    have hn := hs.nowrap
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
    refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = p.op ∧
        t'.gpr .rcx = BitVec.ofNat 64 (16 * p.w)) (by
      xrun [State.ea, hdr, hdi, hdrOff, hl sOut (by decide), hl sK (by decide), hO, hK,
        shr3_w p.k (by omega), sixteen_w _ rfl]) rfl)
      fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨hsi, hcx, (k'.gpr (by decide)).trans hdi⟩
  · -- `main`.
    refine two_map id (fun p t ⟨⟨hs, hdi, hZ, hk1, hk2, hO, hK, hN, hnb, hnl, hpw, _, hps, hz⟩, he⟩ =>
      ⟨hs, hdi, hZ, hk1, hk2, hO, hK, hN, hnb, hnl, ?_, hpw, hps⟩) (pcMain_ct M)
    simp only [eval, hz] at he; simpa using he

/-- The public data of a state. -/
def pcPubOf (s : State) : PcPub :=
  ⟨s.gpr .r8, (s.gpr .r9).toNat * 8, (s.gpr .rcx).toNat, s.gpr .rdi, s.gpr .rdx,
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat⟩

/-- `vg_rsa_public_precompute` is constant time but for `n`. -/
theorem pcCode_constantTime (M : Mont) :
    ConstantTime isa pcContract.pre pcContract.pub (Precompute.code M.mm) := by
  refine RelCT.constantTime ((pcCode_ct M).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨pcPubOf s₁, ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, hn⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, r .r8 (by decide), by rw [r .r9 (by decide)]; rfl, by rw [r .rcx (by decide)]; rfl,
      r .rdi (by decide), r .rdx (by decide), hn.symm⟩

end VG.Proof.Bignum.X86_64
