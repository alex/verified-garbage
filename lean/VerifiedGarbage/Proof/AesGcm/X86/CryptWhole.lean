import VerifiedGarbage.Proof.AesGcm.X86.CryptHead

/-!
# AES-GCM on x86: whole blocks of the text (`cryptWhole`)

Untrusted: everything here is checked by Lean. From a block boundary,
`cryptWhole` encrypts the whole blocks left at `dO` with `vg_aes_ctr32`
(`cryptWhole_pc`), by `Proof.Gcm.ctr_whole`. `ctrArgs_ok` sets up the
arguments of the call, here and in `cryptTail`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K)
include L

/-- `ctrArgs`: the context, the rounds, the counter block and the working space. -/
theorem ctrArgs_ok {R : Nat} {s : State} (he : Env Ctx St W SP s) (hR : RoundsAt s.mem W R) :
    ∃ s', runBlock isa ctrArgs s = some s' ∧ s'.gpr .eax = Ctx ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧
      s'.gpr .edx = St + BitVec.ofNat 32 48 ∧ s'.gpr .ebp = W + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have r₁ := hR.1
  rw [slotv_eq] at r₁
  refine ⟨_, by xrun [ctrArgs, he.ebp, he.esi, L.aW, he.wIn'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · regs [he.ctx]
  · regs [r₁]
  · regs [he.esi]
  · regs [he.ebp]
  · intro r h₁ h₂ h₃ h₄
    simp only [gpr_setMem, gpr_arithFlags, gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂,
      gpr_setReg_of_ne _ _ h₃, gpr_setReg_of_ne _ _ h₄]
  all_goals rfl

variable {R : Nat} {icb : Block} {D : BitVec 32} {n P : Nat}

/-- After `splitWhole`, `nb` whole blocks from byte `j`. -/
structure CWhole1 (j nb : Nat) (m₀ : Mem) (s : State) : Prop where
  at_ : CrAt Ctx St W SP K R icb D n P m₀ j s
  ebx : s.gpr .ebx = D + BitVec.ofNat 32 j
  edi : s.gpr .edi = BitVec.ofNat 32 nb
  zf : s.zf = some (decide (nb = 0))
  dO : slotv s.mem W dO = D + BitVec.ofNat 32 (j + 16 * nb)
  nO : slotv s.mem W nO = BitVec.ofNat 32 ((n - j) % 16)

theorem cWhole1_ok {j : Nat} {m₀ : Mem} {s : State} (h : CrMid Ctx St W SP K R icb D n P m₀ j s) :
    WP isa (.block splitWhole) s (CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R)
      (icb := icb) (D := D) (n := n) (P := P) j ((n - j) / 16) m₀) := by
  have he := h.at_.env
  obtain ⟨s₁, run, bx, di, zf, g, m, rd, wr⟩ := splitWhole_ok L he h.dO h.nO (r := n - j)
    (by have := h.at_.nlt; omega)
  refine WP.of_runBlock ⟨s₁, run, ?_⟩
  have fr : Frame [pslotR W] s.mem s₁.mem := by
    rw [m]; exact pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide) (by decide) _
  refine ⟨h.at_.pslot L fr (g _ (by decide) (by decide) (by decide) (by decide))
      (g _ (by decide) (by decide) (by decide) (by decide)) (g _ (by decide) (by decide) (by decide) (by decide)) rd wr,
    bx, di, zf, ?_, ?_⟩
  · rw [slotv_eq, m]; mems [add_ofNat_assoc32]
  · rw [slotv_eq, m]; mems []

theorem cArgs_ok (hK : K = 28) {j nb : Nat} (hnb : nb ≠ 0) (hj : j + 16 * nb ≤ n) {m₀ : Mem} {s : State}
    (h : CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D) (n := n)
      (P := P) j nb m₀ s) :
    WP isa (.block ctrArgs) s fun s' => CtrReady Ctx St W SP R (St + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb s' ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  subst hK
  have he := h.at_.env
  have hd := h.at_.data
  obtain ⟨s', run, ax, cx, dx, bp, g, m, rd, wr⟩ := ctrArgs_ok L he h.at_.rounds
  refine WP.of_runBlock ⟨s', run, ?_, m, rd, wr⟩
  have hjn : j < n := by omega
  have eP := hd.ok.ptr hjn
  have eC := L.aS (o := 48) (by decide)
  obtain ⟨dr, dst, dw, dk⟩ := hd.ok.part (j := j) (k := 16 * nb) hj
  obtain ⟨dwr, dctx⟩ := hd.part (j := j) (k := 16 * nb) hj
  refine ⟨ax, cx, dx, by rw [g _ (by decide) (by decide) (by decide) (by decide), h.ebx],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), h.edi], bp,
    by rw [g _ (by decide) (by decide) (by decide) (by decide), he.esi],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), he.esp], by rw [rd, wr]; exact he.ctxR,
    by rw [wr]; exact he.stW, by rw [wr]; exact he.wW, by rw [m]; exact he.ctx, by rw [m]; exact h.at_.rounds,
    by rw [L.nS (by decide)]; have := L.fs; omega, by rw [hd.ok.ptrN hjn]; have := hd.ok.fit; omega,
    by rw [wr, eC]; exact he.stC (by decide), by rw [wr, eP]; exact dwr,
    by rw [eC, eP]; exact (dst.sub_right (Lay.stSub (by decide))).symm,
    by rw [eC]; exact L.cs.sub_right (Lay.stSub (by decide)), by rw [eP]; exact dctx,
    by rw [eC]; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
    by rw [eP]; exact dw.sub_right (Lay.wSub (by decide)),
    by rw [eC]; exact L.stk_st (by decide), by rw [eP]; exact dk,
    by rw [eC]; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm,
    by rw [eP]; exact (dw.sub_right (Lay.wSub (by decide))).symm⟩

theorem cArgs_pc (hK : K = 28) {j nb : Nat} (hnb : nb ≠ 0) (hj : j + 16 * nb ≤ n) :
    Pc (CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D) (n := n)
        (P := P) j nb) (.block ctrArgs)
      (fun m₀ s => ∃ s₁, CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb)
        (D := D) (n := n) (P := P) j nb m₀ s₁ ∧
        CtrReady Ctx St W SP R (St + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb s ∧
        s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr) :=
  Pc.taint [.ebp, .esi] (fun m₀ s h => WP.mono (cArgs_ok L hK hnb hj h) fun s' ⟨g, m, rd, wr⟩ => ⟨s, h, g, m, rd, wr⟩)
    (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.at_.env.ebp, h₂.at_.env.ebp]
      · rw [h₁.at_.env.esi, h₂.at_.env.esi]) (by taint_decide)

/-- What `vg_aes_ctr32` writes on the data from `D + j` is apart from the
rest of the data. -/
theorem ctrFr_disj (hK : K = 28) {s : State} (hd : DataW Ctx St W SP K s D n) {j nb a l : Nat}
    (hal : a + l ≤ n) (hsep : a + l ≤ j ∨ j + 16 * nb ≤ a) (hj : j + 16 * nb ≤ n) :
    ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region), ⟨w64 D + BitVec.ofNat 64 j, 16 * nb⟩,
      ⟨w64 W + BitVec.ofNat 64 512, 2048⟩, below SP 28], (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
  subst hK
  have hs : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base _ hal
  have hn := hd.ok.n_lt
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.st.sub_left hs).sub_right (Lay.stSub (by decide))
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · exact (hd.ok.w.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hd.ok.stk.sub_right hs).symm

/-- The slots are apart from what `vg_aes_ctr32` writes. -/
theorem ctrFr_slot (hK : K = 28) {s : State} (hd : DataW Ctx St W SP K s D n) {j nb o : Nat}
    (h₁ : 240 ≤ o) (h₂ : o + 4 ≤ 512) (hj : j + 16 * nb ≤ n) :
    ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region), ⟨w64 D + BitVec.ofNat 64 j, 16 * nb⟩,
      ⟨w64 W + BitVec.ofNat 64 512, 2048⟩, below SP 28], (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := by
  subst hK
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact ((hd.ok.w.sub_left (Offset.sub_base _ hj)).sub_right (Lay.wSub (by omega))).symm
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem ctrFr_crFrame (hK : K = 28) {j nb : Nat} (hj : j + 16 * nb ≤ n) {m m' : Mem}
    (h : Frame [(⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region), ⟨w64 D + BitVec.ofNat 64 j, 16 * nb⟩,
      ⟨w64 W + BitVec.ofNat 64 512, 2048⟩, below SP 28] m m') : Frame (crFrame St W SP K D n) m m' := by
  subst hK
  exact h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ hj⟩
    · exact ⟨wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 28, by simp, fun _ h => h⟩

theorem cWhole3 (hK : K = 28) {j nb : Nat} (hnb : nb ≠ 0) (hnbd : nb = (n - j) / 16) {m₀ : Mem} {s₁ s₂ s' : State}
    (h : CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D) (n := n)
      (P := P) j nb m₀ s₁)
    (m₂ : s₂.mem = s₁.mem) (rd₂ : s₂.rd = s₁.rd) (wr₂ : s₂.wr = s₁.wr)
    (g : CtrOut Ctx St W SP R (St + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb s₂ s') :
    CrMid Ctx St W SP K R icb D n P m₀ (j + 16 * nb) s' := by
  have ha := h.at_
  have hd := ha.data
  have hj : j + 16 * nb ≤ n := by omega
  have hjn : j < n := by omega
  have eP := hd.ok.ptr hjn
  have eC := L.aS (o := 48) (by decide)
  have gf := g.frame
  have go := g.out
  have gc := g.ctr
  rw [eC, eP, m₂] at gf
  rw [eC, eP, m₂] at go
  rw [eC, m₂] at gc
  have hn := hd.ok.n_lt
  have crs := ctrFr_crFrame L (D := D) (n := n) hK hj gf
  have hcm : ciphOf s₁.mem Ctx R = ciphOf m₀ Ctx R := ciph_crFrame L hd ha.frame ha.rounds.2
  rw [hcm] at go
  have hw : (P + j) % 16 = 0 := ha.whole.resolve_left (by omega)
  have hrest16 : bytesAt s₁.mem (w64 D + BitVec.ofNat 64 j) (16 * nb) =
      bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (16 * nb) := by
    have e := congrArg (List.take (16 * nb)) ha.rest
    rwa [bytesAt_take _ _ (by omega), bytesAt_take _ _ (by omega)] at e
  refine ⟨⟨g.env, hj, ha.nlt, hd.of_eq (g.rd.trans rd₂) (g.wr.trans wr₂), g.rounds, fun hc₀ => ?_, fun hc₀ => ?_,
    ?_, .inr (by omega), ha.frame.trans crs⟩, ?_, ?_⟩
  · have := (Proof.Gcm.ctr_whole (ha.ctr hc₀) hw go gc).2
    rwa [Nat.add_assoc] at this
  · have w := (Proof.Gcm.ctr_whole (ha.ctr hc₀) hw go gc).1
    rw [hrest16] at w
    refine done_append ?_ w
    have := ctrFr_disj L hK hd (a := 0) (l := j) (j := j) (nb := nb) (by omega) (.inl (by omega)) hj
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [bytesAt_frame gf this (by omega)]; exact ha.done hc₀
  · rw [bytesAt_frame gf (ctrFr_disj L hK hd (by omega) (.inr (Nat.le_refl _)) hj) (by omega)]
    have e := congrArg (List.drop (16 * nb)) ha.rest
    rw [bytesAt_drop _ _ (by omega), bytesAt_drop _ _ (by omega), add_ofNat_assoc,
      show n - j - 16 * nb = n - (j + 16 * nb) by omega] at e
    exact e
  · rw [slotv_eq, slot_frame gf (ctrFr_slot L hK hd (by decide) (by decide) hj)]; exact h.dO
  · rw [slotv_eq, slot_frame gf (ctrFr_slot L hK hd (by decide) (by decide) hj)]
    have := h.nO; rw [slotv_eq] at this; rw [this]; congr 1; omega

theorem cryptWhole_pc (hK : K = 28) {j : Nat} :
    Pc (CrMid Ctx St W SP K R icb D n P · j) cryptWhole
      (CrMid Ctx St W SP K R icb D n P · (j + 16 * ((n - j) / 16))) := by
  generalize hnb : (n - j) / 16 = nb
  refine Pc.seq (Q := CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D)
      (n := n) (P := P) j nb)
    (hnb ▸ Pc.taint [.ebp] (fun m₀ s h => cWhole1_ok L h)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.at_.env.ebp, h₂.at_.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (nb = 0)) (fun _ _ h => h.zf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s h => ?_
    rw [show j + 16 * 0 = j by omega]
    refine ⟨h.at_, by rw [h.dO, show j + 16 * 0 = j by omega], by rw [h.nO]; congr 1; omega⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hjn : j + 16 * nb ≤ n := by omega
    refine Pc.seq (cArgs_pc L hK h0 hjn) ?_
    exact Pc.mono (Pc.of (I := CtrReady Ctx St W SP R (St + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb)
        (fun _ h => ctrW_ok L hK h) (ctrW_ct L hK) _ fun _ _ ⟨_, _, g, _⟩ => g) (fun _ _ h => h)
      fun m₀ s₃ ⟨s₂, ⟨s₁, h₁, _, m₂, rd₂, wr₂⟩, g₃⟩ => cWhole3 L hK h0 hnb.symm h₁ m₂ rd₂ wr₂ g₃

end

end VG.Proof.AesGcm.X86
