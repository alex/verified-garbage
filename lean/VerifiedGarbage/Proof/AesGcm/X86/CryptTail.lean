import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole

/-!
# AES-GCM on x86: the last bytes of the text (`cryptTail`), and `crypt`

Untrusted: everything here is checked by Lean. From a block boundary with
fewer than 16 bytes left, `cryptTail` makes the next keystream block (the
counter block encrypted onto zeros, by `vg_aes_ctr32`) and XORs it into
them (`cryptTail_pc`), by `Proof.Gcm.ctr_tail`. `crypt_pc`: the three
pieces.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

variable {vg : GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

/-- The regions `vg_aes_ctr32` writes for the keystream block. -/
abbrev ksFrame (St W SP : BitVec 32) : List Region :=
  [⟨w64 St + BitVec.ofNat 64 48, 16⟩, ⟨w64 St + BitVec.ofNat 64 64, 16 * 1⟩, ⟨w64 W + BitVec.ofNat 64 512, 2048⟩,
    below SP 28]

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K)
include L

theorem ksFrame_crFrame (hK : K = 28) {D : BitVec 32} {n : Nat} {m m' : Mem} (h : Frame (ksFrame St W SP) m m') :
    Frame (crFrame St W SP K D n) m m' := by
  subst hK
  exact h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 28, by simp, fun _ h => h⟩

omit L in
theorem ks_crFrame {D : BitVec 32} {n : Nat} {m m' : Mem} (h : Frame [⟨w64 St + BitVec.ofNat 64 64, 16⟩] m m') :
    Frame (crFrame St W SP K D n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩

theorem data_ksFrame (hK : K = 28) {s : State} {D : BitVec 32} {n : Nat} (hd : DataW Ctx St W SP K s D n) {a l : Nat}
    (hal : a + l ≤ n) : ∀ r ∈ ksFrame St W SP, (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
  subst hK
  have hs : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base _ hal
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.st.sub_left hs).sub_right (Lay.stSub (by decide))
  · exact (hd.ok.st.sub_left hs).sub_right (Lay.stSub (by decide))
  · exact (hd.ok.w.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hd.ok.stk.sub_right hs).symm

theorem slot_ksFrame (hK : K = 28) {o : Nat} (h₁ : 240 ≤ o) (h₂ : o + 4 ≤ 512) :
    ∀ r ∈ ksFrame St W SP, (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := by
  subst hK
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

variable {R : Nat} {icb : Block} {D : BitVec 32} {n P : Nat}

/-- The keystream block zeroed, and the arguments of `vg_aes_ctr32` for it. -/
theorem tail1_ok {s : State} (he : Env Ctx St W SP s) (hR : RoundsAt s.mem W R) :
    WP isa (.block (([.mov .eax (imm 0), .store (at_ .esi 64) .eax, .store (at_ .esi 68) .eax,
          .store (at_ .esi 72) .eax, .store (at_ .esi 76) .eax, .mov .ebx (.reg .esi), .alu .add .ebx (imm 64),
          .mov .edi (imm 1)] : List Instr) ++ ctrArgs)) s fun s' =>
      s'.mem = Cmac.zero4 s.mem (w64 St + BitVec.ofNat 64 64) ∧ s'.gpr .eax = Ctx ∧
      s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = St + BitVec.ofNat 32 48 ∧
      s'.gpr .ebp = W + BitVec.ofNat 32 512 ∧ s'.gpr .ebx = St + BitVec.ofNat 32 64 ∧
      s'.gpr .edi = BitVec.ofNat 32 1 ∧ s'.gpr .esi = St ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, m₁, bx, di, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .eax (imm 0), .store (at_ .esi 64) .eax,
      .store (at_ .esi 68) .eax, .store (at_ .esi 72) .eax, .store (at_ .esi 76) .eax, .mov .ebx (.reg .esi),
      .alu .add .ebx (imm 64), .mov .edi (imm 1)] s = some s₁ ∧
      s₁.mem = Cmac.zero4 s.mem (w64 St + BitVec.ofNat 64 64) ∧ s₁.gpr .ebx = St + BitVec.ofNat 32 64 ∧
      s₁.gpr .edi = BitVec.ofNat 32 1 ∧ (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.esi, L.aS, he.stIn], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · mems []; simp only [Proof.Cmac.zero4, Proof.Cmac.store4, add_ofNat_assoc]; rfl
    · regs [he.esi]
    · regs []
    · intro r h₁ h₂ h₃
      simp only [gpr_setMem, gpr_arithFlags, gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂,
        gpr_setReg_of_ne _ _ h₃]
    all_goals rfl
  have fz : Frame [⟨w64 St + BitVec.ofNat 64 64, 16⟩] s.mem s₁.mem := by rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
  have he₁ : Env Ctx St W SP s₁ := he.keep (g₁ _ (by decide) (by decide) (by decide))
    (g₁ _ (by decide) (by decide) (by decide)) (g₁ _ (by decide) (by decide) (by decide)) rd₁ wr₁
    (slot_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm)
  have hR₁ : RoundsAt s₁.mem W R := rounds_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm) hR
  obtain ⟨s₂, run₂, ax, cx, dx, bp, g₂, m₂, rd₂, wr₂⟩ := ctrArgs_ok L he₁ hR₁
  refine WP.of_runBlock ⟨s₂, runBlock_app_of run₁ run₂, by rw [m₂, m₁], ax, cx, dx, bp,
    by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), bx],
    by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), di],
    by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), he₁.esi],
    by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), he₁.esp], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- After the call: the keystream block for the last bytes, and the counter block after it. -/
structure CTail (j : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  le : j ≤ n
  nlt : n < 2 ^ 32
  hlt : n - j < 16
  nz : n - j ≠ 0
  data : DataW Ctx St W SP K s D n
  rounds : RoundsAt s.mem W R
  dO : slotv s.mem W dO = D + BitVec.ofNat 32 j
  nO : slotv s.mem W nO = BitVec.ofNat 32 (n - j)
  ks : CtrS m₀ St (ciphOf m₀ Ctx R) icb P → ∃ m, CtrS m St (ciphOf m₀ Ctx R) icb (P + j) ∧
    blockAt s.mem (w64 St + BitVec.ofNat 64 64) = ciphOf m₀ Ctx R (blockAt m (w64 St + BitVec.ofNat 64 48)) ∧
    blockAt s.mem (w64 St + BitVec.ofNat 64 48) = Spec.Gcm.inc32 (blockAt m (w64 St + BitVec.ofNat 64 48))
  done : CtrS m₀ St (ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem (w64 D) j = xorKs (ciphOf m₀ Ctx R) icb P (bytesAt m₀ (w64 D) j)
  rest : bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (n - j)
  whole : (P + j) % 16 = 0
  frame : Frame (crFrame St W SP K D n) m₀ s.mem

theorem tail2 (hK : K = 28) {j : Nat} (hlt : n - j < 16) (hnz : n - j ≠ 0) {m₀ : Mem} {s₀ s₁ s₂ : State}
    (h : CrMid Ctx St W SP K R icb D n P m₀ j s₀) (m₁ : s₁.mem = Cmac.zero4 s₀.mem (w64 St + BitVec.ofNat 64 64))
    (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr)
    (g : CtrOut Ctx St W SP R (St + BitVec.ofNat 32 48) (St + BitVec.ofNat 32 64) 1 s₁ s₂) :
    CTail (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D) (n := n) (P := P)
      j m₀ s₂ := by
  have ha := h.at_
  have hd := ha.data
  have eC := L.aS (o := 48) (by decide)
  have eK := L.aS (o := 64) (by decide)
  have gf := g.frame
  have go := g.out
  have gc := g.ctr
  rw [eC, eK] at gf go
  rw [eC] at gc
  have fz : Frame [⟨w64 St + BitVec.ofNat 64 64, 16⟩] s₀.mem s₁.mem := by rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
  have zS : ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 64, 16⟩ : Region)], (⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  have zD : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 64, 16⟩ : Region)],
      (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := fun hal r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.ok.st.sub_left (Offset.sub_base _ hal)).sub_right (Lay.stSub (by decide))
  have zW : ∀ {o : Nat}, 96 ≤ o → o + 4 ≤ 2560 → ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 64, 16⟩ : Region)],
      (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.st_w (by decide) (.inr ⟨h₁, h₂⟩)).symm
  have hn := hd.ok.n_lt
  have hcm : ciphOf s₁.mem Ctx R = ciphOf m₀ Ctx R := by
    rw [ciph_crFrame L hd (ks_crFrame fz) ha.rounds.2, ciph_crFrame L hd ha.frame ha.rounds.2]
  rw [hcm] at go
  have hb0 : blockAt s₁.mem (w64 St + BitVec.ofNat 64 64) = 0 := by
    rw [Spec.Gcm.blockAt, m₁, zero4_bytes', ofBytes_zeros]
  rw [blocksAt_one, blocksAt_one, hb0] at go
  have hks := congrArg (fun l => List.getD l 0 0) go
  simp only [List.getD_cons_zero] at hks
  rw [Proof.Gcm.ctr32_getD _ _ _ (by simp)] at hks
  simp only [List.getD_cons_zero, BitVec.zero_xor] at hks
  have hcb : blockAt s₁.mem (w64 St + BitVec.ofNat 64 48) = blockAt s₀.mem (w64 St + BitVec.ofNat 64 48) :=
    blockAt_frame fz zS
  refine ⟨g.env, ha.le, ha.nlt, hlt, hnz, hd.of_eq (g.rd.trans rd₁) (g.wr.trans wr₁), g.rounds, ?_, ?_,
    fun hc₀ => ⟨s₀.mem, ha.ctr hc₀, ?_, ?_⟩, fun hc₀ => ?_, ?_, ha.whole.resolve_left hnz,
    (ha.frame.trans (ks_crFrame fz)).trans (ksFrame_crFrame L hK gf)⟩
  · rw [slotv_eq, slot_frame gf (slot_ksFrame L hK (by decide) (by decide)),
      slot_frame fz (zW (by decide) (by decide))]; exact h.dO
  · rw [slotv_eq, slot_frame gf (slot_ksFrame L hK (by decide) (by decide)),
      slot_frame fz (zW (by decide) (by decide))]; exact h.nO
  · rw [hks, hcb]; simp [Nat.repeat]
  · rw [gc, hcb]; rfl
  · have := data_ksFrame L hK hd (a := 0) (l := j) (by have := ha.le; omega)
    have z := zD (a := 0) (l := j) (by have := ha.le; omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this z
    rw [bytesAt_frame gf this (by omega), bytesAt_frame fz z (by omega)]; exact ha.done hc₀
  · rw [bytesAt_frame gf (data_ksFrame L hK hd (by omega)) (by omega), bytesAt_frame fz (zD (by omega)) (by omega)]
    exact ha.rest

theorem tail3 {j : Nat} {m₀ : Mem} {s : State}
    (h : CTail (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D) (n := n) (P := P)
      j m₀ s) {s' : State}
    (hx : XorPost s (St + BitVec.ofNat 32 64) (D + BitVec.ofNat 32 j) (n - j) s') :
    CrOut Ctx St W SP K R icb D n P m₀ s' := by
  have hd := h.data
  have hjn : j < n := by have := h.nz; omega
  have eP := hd.ok.ptr hjn
  have eK := L.aS (o := 64) (by decide)
  have cm := hx.mem
  rw [eP, eK] at cm
  have hn := hd.ok.n_lt
  have hxl := length_xorBytes s.mem (w64 D + BitVec.ofNat 64 j) (w64 St + BitVec.ofNat 64 64) (n - j)
  have fw : Frame [⟨w64 D + BitVec.ofNat 64 j, n - j⟩] s.mem s'.mem := by rw [cm]; exact writeBytes_frame' _ hxl
  have hf₁ : Frame (crFrame St W SP K D n) s.mem s'.mem := part_crFrame (by omega) fw
  have dS : ∀ {a l : Nat}, a + l ≤ 80 → ∀ r ∈ [(⟨w64 D + BitVec.ofNat 64 j, n - j⟩ : Region)],
      (⟨w64 St + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := fun hal r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.ok.st.sub_left (Offset.sub_base _ (by omega))).sub_right (Lay.stSub hal) |>.symm
  have e := bytesAt_writeBytes_self s.mem (w64 D + BitVec.ofNat 64 j)
    (xorBytes s.mem (w64 D + BitVec.ofNat 64 j) (w64 St + BitVec.ofNat 64 64) (n - j)) (by rw [hxl]; omega)
  rw [hxl] at e
  refine ⟨env_crFrame L hd h.env hf₁ (hx.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (hx.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (hx.other _ (by decide) (by decide) (by decide) (by decide) (by decide)) hx.rd hx.wr,
    rounds_frame hf₁ (kept_crFrame L hd) h.rounds, fun hc₀ => ?_, fun hc₀ => ?_, h.frame.trans hf₁⟩
  · obtain ⟨m, hm, hk, hc⟩ := h.ks hc₀
    have t := (Proof.Gcm.ctr_tail hm h.whole hk hc (d := bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j))
      (by rw [length_bytesAt]; exact h.hlt) (by rw [length_bytesAt]; exact h.nz)).2
    rw [length_bytesAt, show P + j + (n - j) = P + n by omega] at t
    exact t.congr (blockAt_frame fw (dS (by decide))) (blockAt_frame fw (dS (by decide)))
  · obtain ⟨m, hm, hk, hc⟩ := h.ks hc₀
    have t := (Proof.Gcm.ctr_tail hm h.whole hk hc (d := bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j))
      (by rw [length_bytesAt]; exact h.hlt) (by rw [length_bytesAt]; exact h.nz)).1
    rw [length_bytesAt, h.rest] at t
    rw [show n = j + (n - j) by omega]
    refine done_append ?_ ?_
    · have := split_disj (D := w64 D) (j := j) (l := n - j) (by omega)
      rw [bytesAt_frame fw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact this) (by omega)]
      exact h.done hc₀
    · rw [cm, e, xorBytes, h.rest]; exact t

theorem cryptTail_pc (hK : K = 28) {j : Nat} (hlt : n - j < 16) :
    Pc (CrMid Ctx St W SP K R icb D n P · j) (cryptTail vg.callees) (CrOut Ctx St W SP K R icb D n P ·) := by
  refine Pc.seq (Q := fun m₀ s => CrMid Ctx St W SP K R icb D n P m₀ j s ∧ s.zf = some (decide (n - j = 0)))
    (Pc.taint [.ebp] (fun m₀ s h => WP.mono (test_ok L h.at_.env .eax nO (by decide) h.nO
        (by have := h.at_.nlt; omega))
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨h.at_.pslot L (by rw [m]; exact Frame.refl _ _) (g _ (by decide))
          (g _ (by decide)) (g _ (by decide)) rd wr, by rw [m]; exact h.dO, by rw [m]; exact h.nO⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.at_.env.ebp, h₂.at_.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (n - j = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n - j = 0 := by simpa using ht
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨h, _⟩ => ?_
    have ha := h.at_
    have e : j = n := by have := ha.le; omega
    subst e
    exact ⟨ha.env, ha.rounds, ha.ctr, ha.done, ha.frame⟩
  have hnz : n - j ≠ 0 := by simpa using hf
  refine Pc.seq (Q := fun m₀ s => ∃ s₀, CrMid Ctx St W SP K R icb D n P m₀ j s₀ ∧
      s.mem = Cmac.zero4 s₀.mem (w64 St + BitVec.ofNat 64 64) ∧
      CtrReady Ctx St W SP R (St + BitVec.ofNat 32 48) (St + BitVec.ofNat 32 64) 1 s ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr)
    (Pc.taint [.ebp, .esi] (fun m₀ s ⟨h, _⟩ => ?_)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1.at_.env.ebp, h₂.1.at_.env.ebp]
        · rw [h₁.1.at_.env.esi, h₂.1.at_.env.esi]) (by taint_decide)) ?_
  · subst hK
    have he := h.at_.env
    refine WP.mono (tail1_ok L he h.at_.rounds) fun s' ⟨m, ax, cx, dx, bp, bx, di, si, sp, rd, wr⟩ => ⟨s, h, m, ?_, rd, wr⟩
    have eC := L.aS (o := 48) (by decide)
    have eK := L.aS (o := 64) (by decide)
    have fz : Frame [⟨w64 St + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem := by rw [m]; exact Cmac.frame_store4 _ _ _ _ _
    refine ⟨ax, cx, dx, bx, di, bp, si, sp, by rw [rd, wr]; exact he.ctxR, by rw [wr]; exact he.stW,
      by rw [wr]; exact he.wW, ?_, ?_, by rw [L.nS (by decide)]; have := L.fs; omega,
      by rw [L.nS (by decide)]; have := L.fs; omega, by rw [wr, eC]; exact he.stC (by decide),
      by rw [wr, eK]; exact he.stC (by decide), by rw [eC, eK]; exact Lay.st_st (.inl (by decide)) (by decide) (by decide),
      by rw [eC]; exact L.cs.sub_right (Lay.stSub (by decide)), by rw [eK]; exact L.cs.sub_right (Lay.stSub (by decide)),
      by rw [eC]; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
      by rw [eK]; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
      by rw [eC]; exact L.stk_st (by decide), by rw [eK]; exact L.stk_st (by decide),
      by rw [eC]; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm,
      by rw [eK]; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm⟩
    · rw [slot_frame fz fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm]
      exact he.ctx
    · exact rounds_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm)
        h.at_.rounds
  refine Pc.seq (Q := CTail (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb) (D := D)
      (n := n) (P := P) j)
    (Pc.mono (Pc.of (I := CtrReady Ctx St W SP R (St + BitVec.ofNat 32 48) (St + BitVec.ofNat 32 64) 1)
        (fun _ h => ctrW_ok L hK h) (ctrW_ct L hK) _ fun _ _ ⟨_, _, _, g, _⟩ => g) (fun _ _ h => h)
      fun m₀ s₂ ⟨s₁, ⟨s₀, h₀, m₁, _, rd₁, wr₁⟩, g⟩ => tail2 L hK hlt hnz h₀ m₁ rd₁ wr₁ g) ?_
  refine Pc.seq (Q := fun m₀ s => CTail (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (R := R) (icb := icb)
      (D := D) (n := n) (P := P) j m₀ s ∧ s.gpr .edi = D + BitVec.ofNat 32 j ∧ s.gpr .edx = St + BitVec.ofNat 32 64 ∧
      s.gpr .ecx = BitVec.ofNat 32 (n - j))
    (Pc.taint [.ebp, .esi] (fun m₀ s h => ?_)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.env.ebp, h₂.env.ebp]
        · rw [h₁.env.esi, h₂.env.esi]) (by taint_decide)) ?_
  · have he := h.env
    have hd := h.dO
    have hn := h.nO
    refine WP.of_runBlock ⟨_, by xrun [he.ebp, he.esi, L.aW, he.wIn', hd, hn], ?_, ?_, ?_, ?_⟩
    · refine ⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems []), h.le, h.nlt,
        h.hlt, h.nz, h.data.of_eq (by mems []) (by mems []), by mems []; exact h.rounds, by mems []; exact h.dO,
        by mems []; exact h.nO, by mems []; exact h.ks, by mems []; exact h.done, by mems []; exact h.rest, h.whole,
        by mems []; exact h.frame⟩
    · regs []
    · regs [he.esi]
    · regs []
  refine Pc.taint [.edi, .edx, .ecx] (fun m₀ s ⟨h, di, dx, cx⟩ => ?_)
    (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide)
  have he := h.env
  have hdd := h.data
  have hjn : j < n := by have := h.nz; omega
  have eP := hdd.ok.ptr hjn
  have eK := L.aS (o := 64) (by decide)
  obtain ⟨dwr, -⟩ := hdd.part (j := j) (k := n - j) (by omega)
  obtain ⟨-, dst, -, -⟩ := hdd.ok.part (j := j) (k := n - j) (by omega)
  have xp : XorPre s (St + BitVec.ofNat 32 64) (D + BitVec.ofNat 32 j) (n - j) := by
    refine ⟨dx, di, cx, by omega, by have := h.nlt; omega, by rw [L.nS (by decide)]; have := L.fs; omega,
      by rw [hdd.ok.ptrN hjn]; have := hdd.ok.fit; omega, by rw [eK]; exact covers_left (he.stC (by omega)),
      by rw [eP]; exact dwr, by rw [eK, eP]; exact (dst.sub_right (Lay.stSub (by omega))).symm⟩
  exact WP.mono (xorLoop_ok s xp) fun s' x => tail3 L h x

omit L in
theorem CrIn.keep {s s' : State} (h : CrIn Ctx St W SP K R D n P s) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : CrIn Ctx St W SP K R D n P s' :=
  ⟨h.env.keep hbp hsi hsp hrd hwr (by rw [hm]), by rw [hm]; exact h.dO, by rw [hm]; exact h.nO,
    by rw [hm]; exact h.bO, h.nlt, h.data.of_eq hrd hwr, by rw [hm]; exact h.rounds⟩

theorem crypt_pc (hK : K = 28) :
    Pc (fun (m₀ : Mem) s => CrIn Ctx St W SP K R D n P s ∧ s.mem = m₀) (crypt vg.callees)
      (CrOut Ctx St W SP K R icb D n P ·) := by
  have hb16 : P % 16 < 16 := Nat.mod_lt _ (by decide)
  refine Pc.seq (Q := fun m₀ s => (CrIn Ctx St W SP K R D n P s ∧ s.mem = m₀) ∧ s.zf = some (decide (n = 0)))
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => WP.mono (test_ok L h.env .eax nO (by decide) h.nO h.nlt)
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨h.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) m rd wr,
          by rw [m, hm]⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (n = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨h.env, h.rounds, fun hc => ?_, fun _ => ?_,
      by rw [hm]; exact Frame.refl _ _⟩
    · rw [hm]; exact hc
    · rw [hm]; rfl
  have hn0 : n ≠ 0 := by simpa using hf
  refine Pc.seq (Q := fun m₀ s => (CrIn Ctx St W SP K R D n P s ∧ s.mem = m₀) ∧ s.zf = some (decide (P % 16 = 0)))
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨h, hm⟩, _⟩ => WP.mono (test_ok L h.env .eax bO (by decide) h.bO (by omega))
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨h.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) m rd wr,
          by rw [m, hm]⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.env.ebp, h₂.1.1.env.ebp]) (by taint_decide)) ?_
  generalize hj₀ : (if P % 16 = 0 then 0 else min (16 - P % 16) n) = j₀
  have hj₀n : j₀ ≤ n := by rw [← hj₀]; split <;> omega
  refine Pc.seq (Q := (CrMid Ctx St W SP K R icb D n P · j₀)) ?_
    (Pc.seq (cryptWhole_pc L hK) (cryptTail_pc L hK (by omega)))
  refine Pc.ite (decide (P % 16 = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : P % 16 = 0 := by simpa using ht
    simp only [h0, ↓reduceIte] at hj₀
    subst hj₀
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨⟨h.env, Nat.zero_le _, h.nlt, h.data, h.rounds,
      fun hc => by rw [hm]; exact hc, fun _ => by rw [hm]; rfl, by rw [hm], .inr (by omega),
      by rw [hm]; exact Frame.refl _ _⟩, by rw [h.dO]; exact (BitVec.add_zero D).symm, by rw [h.nO, Nat.sub_zero]⟩
  · have h0 : P % 16 ≠ 0 := by simpa using hf
    simp only [h0, ↓reduceIte] at hj₀
    subst hj₀
    exact Pc.mono (cryptHead_pc L hn0 h0) (fun _ _ h => h.1) fun _ _ h => h

end

end VG.Proof.AesGcm.X86
