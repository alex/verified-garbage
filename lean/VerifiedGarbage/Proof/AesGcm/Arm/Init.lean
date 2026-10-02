import VerifiedGarbage.Proof.AesGcm.Arm.Contract

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_init`

Untrusted: everything here is checked by Lean. `init` saves our caller's
registers in `scratch` (`W`), expands the key into the context with
`vg_aes_expand_key`, and computes the hash subkey `CIPH_K(0¹²⁸)` into its
bytes 240–255 with `vg_aes_ctr32` on a zero block, from a zero counter block
at `W + 96` (`init_wp`). The layout lemmas of `Lay` apply with the state
taken to be `W + 16` (which `init` never touches).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt KeyRepr)
open VG.Proof.Cmac (store4)

/-- The number of rounds for a key of `L` bytes, as `init` computes it. -/
theorem roundsOf {L : Nat} (h : L = 16 ∨ L = 24 ∨ L = 32) :
    (BitVec.ofNat 32 L >>> 2) + BitVec.ofNat 32 6 = BitVec.ofNat 32 (Spec.Aes.rounds (L / 4)) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem rounds_ok {L : Nat} (h : L = 16 ∨ L = 24 ∨ L = 32) :
    Spec.Aes.rounds (L / 4) = 10 ∨ Spec.Aes.rounds (L / 4) = 12 ∨ Spec.Aes.rounds (L / 4) = 14 := by
  rcases h with rfl | rfl | rfl <;> decide

/-- The layout, with the state taken to be `W + 16`. -/
theorem initLay {c w sp : BitVec 32} (cw : c.toNat + 256 ≤ 2 ^ 32) (ww : w.toNat + 2560 ≤ 2 ^ 32)
    (sp8 : 8 ≤ sp.toNat) (cW : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr w, 2560⟩)
    (kc : (below sp).Disjoint ⟨State.addr c, 256⟩) (kw : (below sp).Disjoint ⟨State.addr w, 2560⟩) :
    Lay c (w + BitVec.ofNat 32 16) w sp := by
  have e : State.addr (w + BitVec.ofNat 32 16) = State.addr w + BitVec.ofNat 64 16 := addr_add (by omega)
  have hs : Region.Sub ⟨State.addr w + BitVec.ofNat 64 16, 80⟩ ⟨State.addr w, 2560⟩ := Lay.wSub (by decide)
  refine ⟨cw, ?_, ww, sp8, ?_, cW, ?_, ?_, kc, ?_, kw⟩
  · rw [show (w + BitVec.ofNat 32 16).toNat = w.toNat + 16 by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), Nat.mod_eq_of_lt (by omega)]]
    omega
  · rw [e]; exact cW.sub_right hs
  · rw [e]; simpa using Lay.w_w (w := w) (a := 16) (n := 80) (d := 0) (k := 16) (.inr (by decide)) (by decide)
      (by decide)
  · rw [e]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [e]; exact kw.sub_right hs

/-- The entry: our caller's registers saved, `W` in `r11`, the context in
`r9`, the number of rounds in `r8`, and the working space of the key
expansion in `r3`. -/
theorem initPre_ok {s₀ : State} (hfit : (s₀.gpr .r3).toNat + 2560 ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr (s₀.gpr .r3), 2560⟩] s₀.wr) {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr .r11 = s₀.gpr .r3 → s₁.gpr .r9 = s₀.gpr .r2 →
      s₁.gpr .r8 = (s₀.gpr .r1 >>> 2) + BitVec.ofNat 32 6 → s₁.gpr .r3 = s₀.gpr .r3 + BitVec.ofNat 32 512 →
      s₁.gpr .r0 = s₀.gpr .r0 → s₁.gpr .r1 = s₀.gpr .r1 → s₁.gpr .r2 = s₀.gpr .r2 →
      s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp → SavedAt s₁.mem (s₀.gpr .r3) s₀ →
      Frame [savedR (s₀.gpr .r3)] s₀.mem s₁.mem → Q s₁) :
    WP isa (.block initPre) s₀ Q := by
  unfold initPre
  refine save_ok rfl hfit hw fun s' g rd wr sp sv fr => WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rd wr sp sv fr
  all_goals simp [gpr_setReg, g]

/-- The hash subkey's block and `T` zeroed, and the arguments of
`vg_aes_ctr32` on them. -/
theorem initArgs_ok {c w sp k8 : BitVec 32} (L : Lay c (w + BitVec.ofNat 32 16) w sp) {s : State}
    (h9 : s.gpr .r9 = c) (h11 : s.gpr .r11 = w) (h8 : s.gpr .r8 = k8) (hc : Covers [⟨State.addr c, 256⟩] s.wr)
    (hw : Covers [⟨State.addr w, 2560⟩] s.wr) :
    ∃ s', runBlock isa initArgs s = some s' ∧
      s'.mem = store4 (store4 s.mem (State.addr c + BitVec.ofNat 64 240) 0 0 0 0)
        (State.addr w + BitVec.ofNat 64 96) 0 0 0 0 ∧
      s'.gpr .r0 = c ∧ s'.gpr .r1 = k8 ∧ s'.gpr .r2 = w + BitVec.ofNat 32 96 ∧
      s'.gpr .r3 = c + BitVec.ofNat 32 240 ∧ s'.gpr .r12 = BitVec.ofNat 32 1 ∧
      s'.gpr .lr = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have c₀ := in_off hc (show 240 + 4 ≤ 256 by decide) (by decide)
  have c₁ := in_off hc (show 244 + 4 ≤ 256 by decide) (by decide)
  have c₂ := in_off hc (show 248 + 4 ≤ 256 by decide) (by decide)
  have c₃ := in_off hc (show 252 + 4 ≤ 256 by decide) (by decide)
  have w₀ := in_off hw (show 96 + 4 ≤ 2560 by decide) (by decide)
  have w₁ := in_off hw (show 100 + 4 ≤ 2560 by decide) (by decide)
  have w₂ := in_off hw (show 104 + 4 ≤ 2560 by decide) (by decide)
  have w₃ := in_off hw (show 108 + 4 ≤ 2560 by decide) (by decide)
  refine ⟨_, by simp only [initArgs]; arun [h9, h11, L.cA, L.wA, c₀, c₁, c₂, c₃, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]; rfl
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg, h8]
  · simp [gpr_setReg, h11]
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg]
  · simp [gpr_setReg, h11]
  · intro r a b d e f i; simp [gpr_setReg, a, b, d, e, f, i]
  all_goals rfl

theorem zero_block (m : Mem) (p : Addr) : blockAt (store4 m p 0 0 0 0) p = 0 := by
  rw [blockAt, Cmac.bytesAt_store4, Cmac.le4_zero]; decide

/-- After the entry, from `s₀`. -/
structure IS1 (s₀ s₁ : State) : Prop where
  r11 : s₁.gpr .r11 = s₀.gpr .r3
  r9 : s₁.gpr .r9 = s₀.gpr .r2
  r8 : s₁.gpr .r8 = (s₀.gpr .r1 >>> 2) + BitVec.ofNat 32 6
  r3 : s₁.gpr .r3 = s₀.gpr .r3 + BitVec.ofNat 32 512
  r0 : s₁.gpr .r0 = s₀.gpr .r0
  r1 : s₁.gpr .r1 = s₀.gpr .r1
  r2 : s₁.gpr .r2 = s₀.gpr .r2
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr
  sp : s₁.sp = s₀.sp
  saved : SavedAt s₁.mem (s₀.gpr .r3) s₀
  frame : Frame [savedR (s₀.gpr .r3)] s₀.mem s₁.mem

/-- The number of rounds of `init`'s key. -/
abbrev initR (s₀ : State) : Nat := Spec.Aes.rounds ((s₀.gpr .r1).toNat / 4)

theorem is1_wp {s₀ : State} (h : initArm.pre s₀) : WP isa (.block initPre) s₀ (IS1 s₀) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, fs, -, -⟩ := h
  exact initPre_ok fs (by rw [hwr]; exact covers_of_mem (by simp))
    fun s₁ a b c d e f g h i j k l => ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩

theorem init_kc {s₀ s₁ : State} (h : initArm.pre s₀) (h1 : IS1 s₀ s₁) :
    KeyCall s₁ (s₀.gpr .r0) (s₀.gpr .r2) (s₀.gpr .r3 + BitVec.ofNat 32 512) (s₀.gpr .r1).toNat := by
  obtain ⟨hrd, hwr, dkc, dks, dcs, bk, bc, bs, fk, fc, fs, sp8, hlen⟩ := h
  have L := initLay fc fs sp8 dcs bc bs
  have hW : Covers [⟨State.addr (s₀.gpr .r3), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hC : Covers [⟨State.addr (s₀.gpr .r2), 256⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have eS := L.wA (d := 512) (by decide)
  refine ⟨h1.r0, by rw [h1.r1]; simp, h1.r2, h1.r3, hlen, fk, by omega, by rw [L.wN (by decide)]; omega,
    dkc.sub_right (Region.sub_prefix (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [eS]; exact dks.sub_right (Lay.wSub (by decide))
  · rw [eS]; exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · rw [h1.rd, h1.wr, hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _))
  · rw [h1.wr, eS]
    exact covers_cons (covers_prefix hC (by decide)) (covers_cons (covers_off hW (by decide) (by decide)) covers_nil)

/-- After the key expansion. -/
def IS2 (s₀ s₂ : State) : Prop :=
  ∃ s₁, IS1 s₀ s₁ ∧ KeyPost s₁ (s₀.gpr .r0) (s₀.gpr .r2) (s₀.gpr .r3 + BitVec.ofNat 32 512) (s₀.gpr .r1).toNat s₂

/-- After `initArgs`. -/
def IS3 (s₀ s₃ : State) : Prop := ∃ s₂, IS2 s₀ s₂ ∧ runBlock isa initArgs s₂ = some s₃

theorem IS2.g {s₀ s₂ : State} (h : IS2 s₀ s₂) : s₂.gpr .r9 = s₀.gpr .r2 ∧ s₂.gpr .r11 = s₀.gpr .r3 ∧
    s₂.gpr .r8 = (s₀.gpr .r1 >>> 2) + BitVec.ofNat 32 6 ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr ∧ s₂.sp = s₀.sp := by
  obtain ⟨s₁, h1, kp⟩ := h
  exact ⟨by rw [kp.saved .r9 (by decide) (by decide), h1.r9], by rw [kp.saved .r11 (by decide) (by decide), h1.r11],
    by rw [kp.saved .r8 (by decide) (by decide), h1.r8], kp.rd.trans h1.rd, kp.wr.trans h1.wr, kp.sp.trans h1.sp⟩

/-- What `initArgs` leaves. -/
theorem IS3.facts {s₀ s₃ : State} (h : initArm.pre s₀) (h3 : IS3 s₀ s₃) :
    ∃ s₂, IS2 s₀ s₂ ∧
      s₃.mem = store4 (store4 s₂.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 240) 0 0 0 0)
        (State.addr (s₀.gpr .r3) + BitVec.ofNat 64 96) 0 0 0 0 ∧
      s₃.gpr .r0 = s₀.gpr .r2 ∧ s₃.gpr .r1 = BitVec.ofNat 32 (initR s₀) ∧
      s₃.gpr .r2 = s₀.gpr .r3 + BitVec.ofNat 32 96 ∧
      s₃.gpr .r3 = s₀.gpr .r2 + BitVec.ofNat 32 240 ∧ s₃.gpr .r12 = BitVec.ofNat 32 1 ∧
      s₃.gpr .lr = s₀.gpr .r3 + BitVec.ofNat 32 512 ∧ s₃.gpr .r11 = s₀.gpr .r3 ∧
      s₃.rd = s₀.rd ∧ s₃.wr = s₀.wr ∧ s₃.sp = s₀.sp := by
  obtain ⟨s₂, h2, run⟩ := h3
  obtain ⟨-, hwr, -, -, dcs, -, bc, bs, -, fc, fs, sp8, hlen⟩ := h
  have L := initLay fc fs sp8 dcs bc bs
  obtain ⟨g9, g11, g8, grd, gwr, gsp⟩ := h2.g
  have hr8 : s₀.gpr .r1 >>> 2 + BitVec.ofNat 32 6 = BitVec.ofNat 32 (initR s₀) := by
    have := roundsOf hlen; rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  obtain ⟨s₃', run', hm, g0, g1, g2, g3, g12, glr, gg, rd, wr, sp⟩ := initArgs_ok L (s := s₂) g9 g11 g8
    (by rw [gwr, hwr]; exact covers_of_mem (by simp)) (by rw [gwr, hwr]; exact covers_of_mem (by simp))
  obtain rfl : s₃' = s₃ := Option.some.inj (run'.symm.trans run)
  exact ⟨s₂, h2, hm, g0, g1.trans hr8, g2, g3, g12, glr,
    by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g11],
    rd.trans grd, wr.trans gwr, sp.trans gsp⟩

theorem init_cc {s₀ s₃ : State} (h : initArm.pre s₀) (h3 : IS3 s₀ s₃) :
    CtrCall s₃ (s₀.gpr .r2) (s₀.gpr .r3 + BitVec.ofNat 32 96) (s₀.gpr .r2 + BitVec.ofNat 32 240)
      (s₀.gpr .r3 + BitVec.ofNat 32 512) (initR s₀) 1 := by
  obtain ⟨s₂, -, -, g0, g1, g2, g3, g12, glr, -, -, wr₃, hk3⟩ := h3.facts h
  obtain ⟨-, hwr, -, -, dcs, -, bc, bs, -, fc, fs, sp8, hlen⟩ := h
  have L := initLay fc fs sp8 dcs bc bs
  have hW : Covers [⟨State.addr (s₀.gpr .r3), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hC : Covers [⟨State.addr (s₀.gpr .r2), 256⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have eS := L.wA (d := 512) (by decide)
  have eT := L.wA (d := 96) (by decide)
  have eH := L.cA (d := 240) (by decide)
  refine ⟨g0, g1, g2, g3, g12, glr, rounds_ok hlen, by rw [hk3]; exact sp8,
    by omega, by rw [L.wN (by decide)]; omega, by rw [L.cN (by decide)]; omega, by rw [L.wN (by decide)]; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [eS, eT, eH, hk3]
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · simpa using Lay.ctx_ctx (c := s₀.gpr .r2) (a := 0) (n := 240) (d := 240) (k := 16) (.inl (by decide))
      (by decide) (by decide)
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · exact (L.ctx_w (a := 240) (n := 16) (d := 96) (k := 16) (by decide) (by decide)).symm
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.kc.sub_right (Region.sub_prefix (by decide))
  · exact L.stk_w (by decide)
  · exact L.stk_ctx (by decide)
  · exact L.stk_w (by decide)
  · rw [wr₃]; exact covers_left (covers_prefix hC (by decide))
  · rw [wr₃]
    exact covers_cons (covers_off hW (by decide) (by decide))
      (covers_cons (covers_off hC (by decide) (by decide)) (covers_cons (covers_off hW (by decide) (by decide))
        covers_nil))

/-- After the call of `vg_aes_ctr32`. -/
def IS4 (s₀ s₄ : State) : Prop :=
  ∃ s₃, IS3 s₀ s₃ ∧ CtrPost s₃ (s₀.gpr .r2) (s₀.gpr .r3 + BitVec.ofNat 32 96) (s₀.gpr .r2 + BitVec.ofNat 32 240)
      (s₀.gpr .r3 + BitVec.ofNat 32 512) (initR s₀) 1 s₄

theorem init_fin {s₀ s₄ : State} (h : initArm.pre s₀) (h4 : IS4 s₀ s₄) :
    WP isa (.block restore) s₄ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' := by
  obtain ⟨s₃, h3, cp⟩ := h4
  obtain ⟨s₂, h2, hm₃, -, -, -, -, -, -, g11, -, wr₃, hk3⟩ := h3.facts h
  obtain ⟨s₁, h1, kp⟩ := h2
  obtain ⟨-, hwr, -, dks, dcs, -, bc, bs, -, fc, fs, sp8, hlen⟩ := h
  have L := initLay fc fs sp8 dcs bc bs
  have hR := rounds_ok hlen
  have hW : Covers [⟨State.addr (s₀.gpr .r3), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have eS := L.wA (d := 512) (by decide)
  have eT := L.wA (d := 96) (by decide)
  have eH := L.cA (d := 240) (by decide)
  have dSv : ∀ {d k : Nat}, d + k ≤ 2560 → (128 + 36 ≤ d ∨ d + k ≤ 128) →
      (savedR (s₀.gpr .r3)).Disjoint ⟨State.addr (s₀.gpr .r3) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Lay.w_w (by omega) (by decide) h₁
  have dSc : ∀ {d k : Nat}, d + k ≤ 256 →
      (savedR (s₀.gpr .r3)).Disjoint ⟨State.addr (s₀.gpr .r2) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => (L.ctx_w h₁ (show 128 + 36 ≤ 2560 by decide)).symm
  have cframe := cp.frame
  have cout := cp.out
  simp only [eS, eT, eH, hk3] at cframe cout
  have f₃ : Frame [⟨State.addr (s₀.gpr .r2) + BitVec.ofNat 64 240, 16⟩, ⟨State.addr (s₀.gpr .r3) + BitVec.ofNat 64 96, 16⟩]
      s₂.mem s₃.mem := by
    rw [hm₃]
    exact ((Cmac.frame_store4 _ 0 0 0 0).mono (by simp)).trans ((Cmac.frame_store4 _ 0 0 0 0).mono (by simp))
  have kframe := kp.frame
  rw [eS] at kframe
  have sv₄ : SavedAt s₄.mem (s₀.gpr .r3) s₀ := by
    refine ((h1.saved.frame kframe ?_).frame f₃ ?_).frame cframe ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa using dSc (d := 0) (k := 240) (by decide)
      · exact dSv (by decide) (.inl (by decide))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dSc (by decide)
      · exact dSv (by decide) (.inr (by decide))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact dSv (by decide) (.inr (by decide))
      · exact dSc (by decide)
      · exact dSv (by decide) (.inl (by decide))
      · exact (L.stk_w (show 128 + 36 ≤ 2560 by decide)).symm
  refine WP.mono (restore_ok (s₀ := s₀) (by rw [cp.saved _ (by decide) (by decide), g11]) fs
      (by rw [cp.wr, wr₃]; exact covers_left hW) sv₄ (by rw [cp.sp, hk3])) fun s' hh => ⟨hh.1, ?_⟩
  have hm := hh.2.1
  have hRb : 16 * (initR s₀ + 1) ≤ 240 := by simp only [initR]; rcases hR with h' | h' | h' <;> omega
  have dP : ∀ {d k : Nat}, 240 ≤ d → d + k ≤ 256 →
      (⟨State.addr (s₀.gpr .r2), 16 * (initR s₀ + 1)⟩ : Region).Disjoint
        ⟨State.addr (s₀.gpr .r2) + BitVec.ofNat 64 d, k⟩ := fun {d k} h₁ h₂ => by
    simpa using Lay.ctx_ctx (c := s₀.gpr .r2) (a := 0) (n := 16 * (initR s₀ + 1))
      (d := d) (k := k) (.inl (by simp only [initR] at hRb ⊢; omega)) (by simp only [initR] at hRb ⊢; omega) h₂
  have dPw : ∀ {d k : Nat}, d + k ≤ 2560 →
      (⟨State.addr (s₀.gpr .r2), 16 * (initR s₀ + 1)⟩ : Region).Disjoint
        ⟨State.addr (s₀.gpr .r3) + BitVec.ofNat 64 d, k⟩ := fun h₁ =>
    (L.cw'.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub h₁)
  have ks₃ : bytesAt s₃.mem (State.addr (s₀.gpr .r2)) (16 * (initR s₀ + 1)) =
      Spec.Aes.expandKey (bytesAt s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) := by
    rw [bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dP (Nat.le_refl _) (by decide)
        · exact dPw (by decide)) (by omega), kp.out,
      bytesAt_frame h1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dks.sub_right (Lay.wSub (by decide))) (by omega)]
  simp only [initArm, KeyRepr, length_bytesAt, hm]
  refine ⟨?_, ?_⟩
  · rw [bytesAt_frame cframe (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact dPw (by decide)
        · exact dP (Nat.le_refl _) (by decide)
        · exact dPw (by decide)
        · exact (L.kc.sub_right (Region.sub_prefix (by omega))).symm) (by omega), ks₃]
  · rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at cout
    have z₁ : blockAt s₃.mem (State.addr (s₀.gpr .r3) + BitVec.ofNat 64 96) = 0 := by rw [hm₃, zero_block]
    have z₂ : blockAt s₃.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 240) = 0 := by
      rw [hm₃, blockAt_frame (Cmac.frame_store4 _ 0 0 0 0) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.ctx_w (by decide) (by decide)), zero_block]
    rw [ctxH_eq, cout.1, z₁, z₂]
    refine BitVec.zero_xor.trans ?_
    rw [ks₃, Spec.Gcm.aes, length_bytesAt]

theorem is3_run {s₀ s₂ : State} (h : initArm.pre s₀) (h2 : IS2 s₀ s₂) : ∃ s₃, runBlock isa initArgs s₂ = some s₃ := by
  obtain ⟨-, hwr, -, -, dcs, -, bc, bs, -, fc, fs, sp8, -⟩ := h
  obtain ⟨g9, g11, -, -, gwr, -⟩ := h2.g
  obtain ⟨s₃, run, -⟩ := initArgs_ok (initLay fc fs sp8 dcs bc bs) (s := s₂) g9 g11 rfl
    (by rw [gwr, hwr]; exact covers_of_mem (by simp)) (by rw [gwr, hwr]; exact covers_of_mem (by simp))
  exact ⟨s₃, run⟩

theorem init_wp {s₀ : State} (h : initArm.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' :=
  WP.seq (WP.mono (is1_wp h) fun s₁ h1 => WP.seq (WP.mono (key_call (init_kc h h1)) fun s₂ kp =>
    WP.seq (by
      obtain ⟨s₃, run⟩ := is3_run h ⟨s₁, h1, kp⟩
      exact WP.of_runBlock ⟨s₃, run, WP.seq (WP.mono (ctr_call (init_cc h ⟨s₂, ⟨s₁, h1, kp⟩, run⟩)) fun s₄ cp =>
        init_fin h ⟨s₃, ⟨s₂, ⟨s₁, h1, kp⟩, run⟩, cp⟩)⟩)))

end VG.Proof.AesGcm.Arm
