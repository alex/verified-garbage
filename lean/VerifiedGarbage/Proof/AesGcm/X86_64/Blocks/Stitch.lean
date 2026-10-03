import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Mid
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec

/-!
# AES-GCM on whole blocks, x86-64: the first `16 ⌊n / 16⌋` blocks in one pass

Untrusted: everything here is checked by Lean. After the entry, if there are
at least 16 blocks, `r9` becomes `16 ⌊n / 16⌋` (`split_ok`), which with the
other arguments still in their registers meets what the interleaved loops
need (`spre_of`); their result is `Mid` with `q = 16 ⌊n / 16⌋`
(`mid_of_post`). With fewer, `q = 0` (`stitchE_ok`, `stitchD_ok`); then `rest`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- The registers the entry leaves as they were. -/
def argRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8]

theorem contains_prefix (a : Addr) {k L : Nat} (h : k ≤ L) : (⟨a, L⟩ : Region).Contains a k := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

section
variable {s : State} (hp : BP s)
include hp

omit hp in
/-- `r9 := 16 ⌊r9 / 16⌋`. -/
theorem split_ok {s₁ : State} (h9 : s₁.gpr .r9 = s.gpr .r9) :
    WP isa (.block [.mov .rax (.reg .r9), .alu .and .rax (imm 15), .alu .sub .r9 (.reg .rax)]) s₁ fun s₃ =>
      s₃.gpr .r9 = BitVec.ofNat 64 (n s - n s % 16) ∧ (∀ r, r ≠ .rax → r ≠ .r9 → s₃.gpr r = s₁.gpr r) ∧
      s₃.mem = s₁.mem ∧ s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have e15 := and15 (s.gpr .r9)
  rw [imm_eq (by decide)] at e15
  have esub : s.gpr .r9 - BitVec.ofNat 64 (n s % 16) = BitVec.ofNat 64 (n s - n s % 16) := by
    rw [← ofNat_sub (Nat.mod_le _ _) hn]; simp
  apply WP.of_runBlock
  refine ⟨_, by xrun [h9, e15, esub], ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- What the interleaved loops need, from the arguments in their registers
and `r9 = 16 ⌊n / 16⌋`. -/
theorem spre_of {s₃ : State} (h16 : 16 ≤ n s) (h9 : s₃.gpr .r9 = BitVec.ofNat 64 (n s - n s % 16))
    (hg : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r) (h11 : s₃.gpr .r11 = S s) (hrd : s₃.rd = s.rd)
    (hwr : s₃.wr = fR s :: s.wr) : Gcm.X86_64.Stitch.SPre s₃ := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hq : (s₃.gpr .r9).toNat = n s - n s % 16 := by rw [h9, toNat_ofNat_of_lt (by omega)]
  have hqn : 16 * (n s - n s % 16) ≤ n s * 16 := by omega
  have pd : Region.Sub ⟨D s, 16 * (n s - n s % 16)⟩ (dR s) := Region.sub_prefix hqn
  have ps : Region.Sub ⟨S s, 256⟩ (sR s) := Region.sub_prefix (by decide)
  have ek : s₃.gpr .rdi = K s := hg _ (by simp [argRegs])
  have er : s₃.gpr .rsi = s.gpr .rsi := hg _ (by simp [argRegs])
  have ec : s₃.gpr .rdx = C s := hg _ (by simp [argRegs])
  have ey : s₃.gpr .rcx = Y s := hg _ (by simp [argRegs])
  have ed : s₃.gpr .r8 = D s := hg _ (by simp [argRegs])
  have wr : s.wr = wR s := hp.wr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [Gcm.X86_64.Stitch.nr, Gcm.X86_64.Stitch.nb, Gcm.X86_64.Stitch.kp,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.pp,
    Gcm.X86_64.Stitch.kR, Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.yR, Gcm.X86_64.Stitch.dR,
    Gcm.X86_64.Stitch.pR, ek, er, ec, ey, ed, h11, hq, hrd, hwr]
  exacts [hp.rounds, by omega, by omega, ⟨kR s, by rw [hp.rd]; simp, Region.contains_self _ _⟩,
    ⟨cR s, by rw [wr]; simp, Region.contains_self _ _⟩, ⟨yR s, by rw [wr]; simp, Region.contains_self _ _⟩,
    ⟨dR s, by rw [wr]; simp, contains_prefix _ hqn⟩, ⟨sR s, by rw [wr]; simp, contains_prefix _ (by decide)⟩,
    hp.k_d.symm.sub_left pd, hp.c_d.symm.sub_left pd, hp.y_d.symm.sub_left pd,
    (hp.d_s.sub_left pd).sub_right ps, hp.k_s.symm.sub_left ps, hp.c_s.symm.sub_left ps,
    hp.y_s.symm.sub_left ps, hp.c_y, hp.k_c.symm, hp.k_y.symm, by have := hp.w_d; omega, hp.w_k,
    by have := hp.w_s; omega]

/-- The hash subkey is apart from the frame. -/
theorem fR_disj' : (⟨K s + 240, 16⟩ : Region).Disjoint (fR s) :=
  (hp.t_k.symm.sub_right fR_sub).sub_left (Offset.sub_base (d := 240) _ (by decide))

/-- The data from block `q` on, apart from the first `q` blocks and from the
other regions written. -/
theorem rest_disj {q : Nat} (hq : q ≤ n s) :
    ∀ r ∈ [cR s, yR s, (⟨D s, 16 * q⟩ : Region), (⟨S s, 256⟩ : Region)],
      (⟨dq s q, 16 * (n s - q)⟩ : Region).Disjoint r := by
  have hsub : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) := Offset.sub_base _ (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.c_d.symm.sub_left hsub
  · exact hp.y_d.symm.sub_left hsub
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.w_d; omega)
  · exact (hp.d_s.sub_left hsub).sub_right (Region.sub_prefix (by decide))

/-- `Mid` after the interleaved loops, from what they leave. -/
theorem mid_of_post {s₃ s₄ : State} (h9 : s₃.gpr .r9 = BitVec.ofNat 64 (n s - n s % 16))
    (hg : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r) (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → s₃.gpr r = s.gpr r)
    (hsp : s₃.gpr .rsp = F s) (h11 : s₃.gpr .r11 = S s)
    (hrd : s₃.rd = s.rd) (hwr : s₃.wr = fR s :: s.wr) (hkp : Kept s 0 s₃.mem) (hf₃ : Frame [fR s] s.mem s₃.mem)
    (data : blocksAt s₄.mem (s₃.gpr .r8) (s₃.gpr .r9).toNat = ctr32 (Gcm.X86_64.Stitch.ciph s₃)
      (blockAt s₃.mem (s₃.gpr .rdx)) (blocksAt s₃.mem (s₃.gpr .r8) (s₃.gpr .r9).toNat))
    (ctr : blockAt s₄.mem (s₃.gpr .rdx) = Nat.repeat inc32 (s₃.gpr .r9).toNat (blockAt s₃.mem (s₃.gpr .rdx)))
    (frame : Frame [Gcm.X86_64.Stitch.cR s₃, Gcm.X86_64.Stitch.yR s₃, Gcm.X86_64.Stitch.dR s₃,
      Gcm.X86_64.Stitch.pR s₃] s₃.mem s₄.mem)
    (gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s₃.gpr r)
    (rd : s₄.rd = s₃.rd) (wr : s₄.wr = s₃.wr) {ys : List Block}
    (y : blockAt s₃.mem (K s + 240) = hk s → blockAt s₃.mem (Y s) = y₀ s →
      blocksAt s₃.mem (D s) (n s - n s % 16) = blocksAt s.mem (D s) (n s - n s % 16) →
      blocksAt s₄.mem (D s) (n s - n s % 16) = ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (n s - n s % 16)) →
      blockAt s₄.mem (Y s) = ghashFrom (hk s) (y₀ s) ys) :
    Mid s (n s - n s % 16) 0 ys s₄ := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  generalize hq : n s - n s % 16 = q at *
  have hqn : q ≤ n s := by omega
  have hq9 : (s₃.gpr .r9).toNat = q := by rw [h9, toNat_ofNat_of_lt (by omega)]
  have ek : s₃.gpr .rdi = K s := hg _ (by simp [argRegs])
  have er : s₃.gpr .rsi = s.gpr .rsi := hg _ (by simp [argRegs])
  have ec : s₃.gpr .rdx = C s := hg _ (by simp [argRegs])
  have ey : s₃.gpr .rcx = Y s := hg _ (by simp [argRegs])
  have ed : s₃.gpr .r8 = D s := hg _ (by simp [argRegs])
  simp only [Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.yR, Gcm.X86_64.Stitch.dR, Gcm.X86_64.Stitch.pR,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.pp,
    Gcm.X86_64.Stitch.nb, ec, ey, ed, h11, hq9] at frame
  rw [ed, hq9, ec] at data
  rw [ec, hq9] at ctr
  simp only [Gcm.X86_64.Stitch.ciph, Gcm.X86_64.Stitch.sch, Gcm.X86_64.Stitch.nr, Gcm.X86_64.Stitch.kp, ek,
    er] at data
  have kd : ∀ r ∈ [fR s], (kR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.t_k.symm.sub_right fR_sub
  have hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  have eK : Spec.Aes.bytesAt s₃.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) :=
    bytesAt_frame hf₃ (fun r hr => (kd r hr).sub_left (Region.sub_prefix hRb)) (by omega)
  have eC : blockAt s₃.mem (C s) = cb s := block_fR hf₃ (fR_disj hp _ (by simp)).symm
  have pd : Region.Sub ⟨D s, 16 * q⟩ (dR s) := Region.sub_prefix (by omega)
  have eD : blocksAt s₃.mem (D s) q = blocksAt s.mem (D s) q := blocksAt_frame hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (fR_disj hp (dR s) (by simp)).symm.sub_left pd)
    (by have := hp.w_d; omega)
  rw [eK, eC, eD] at data
  rw [eC] at ctr
  have y' := y (block_fR hf₃ (fR_disj' hp)) (block_fR hf₃ (fR_disj hp _ (by simp)).symm) eD data
  have fk : ∀ r ∈ [cR s, yR s, (⟨D s, 16 * q⟩ : Region), (⟨S s, 256⟩ : Region)], (fR s).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact fR_disj hp _ (by simp)
    · exact fR_disj hp _ (by simp)
    · exact (fR_disj hp (dR s) (by simp)).sub_right pd
    · exact (fR_disj hp (sR s) (by simp)).sub_right (Region.sub_prefix (by decide))
  have fw : Frame (tR s :: wR s) s.mem s₄.mem := by
    refine (hf₃.sub fun r hr => ?_).trans (frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨tR s, by simp, fR_sub⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨cR s, by simp, fun _ h => h⟩
      · exact ⟨yR s, by simp, fun _ h => h⟩
      · exact ⟨dR s, by simp, pd⟩
      · exact ⟨sR s, by simp, Region.sub_prefix (by decide)⟩
  have hw := hp.w_d
  refine ⟨hqn, ?_, fun r hr h' => ?_, rd.trans hrd, wr.trans hwr, hkp.frame frame fk, fw, data, ?_, ctr, y'⟩
  · rw [gpr _ (by decide) (by decide) (by decide) (by decide)]; exact hsp
  · have hr' : r ≠ .rax ∧ r ≠ .rdx ∧ r ≠ .r9 ∧ r ≠ .r10 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gpr r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2]; exact hcs r hr h'
  · rw [blocksAt_frame frame (rest_disj hp hqn) (by omega)]
    exact blocksAt_frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (fR_disj hp (dR s) (by simp)).symm.sub_left (Offset.sub_base _ (by omega))) (by omega)

omit hp in
/-- `cmp r9, 16`. -/
theorem cmp16_ok {s₁ : State} (h9 : s₁.gpr .r9 = s.gpr .r9) :
    WP isa (.block [.alu .cmp .r9 (imm 16)]) s₁ fun s₂ => s₂.gpr = s₁.gpr ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.cf = some (decide (n s < 16)) := by
  have e16 : BitVec.signExtend 64 (BitVec.ofNat 32 16) = 16 := by decide
  apply WP.of_runBlock
  simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
    isa, e16, h9, Option.bind_some, Option.some.injEq, exists_eq_left']
  simp

/-- The interleaved part and `rest`, from the state after the entry, given
what the loops leave (`post`) as `Mid` for the blocks hashed `ys q`. -/
theorem stitch_ok {piece : Prog isa} {Post : State → State → Prop} {ys : Nat → List Block}
    (hys : ys 0 = [])
    (hpiece : ∀ s₃, Gcm.X86_64.Stitch.SPre s₃ → WP isa piece s₃ (Post s₃))
    (hpost : ∀ s₃ s₄, s₃.gpr .r9 = BitVec.ofNat 64 (n s - n s % 16) → (∀ r ∈ argRegs, s₃.gpr r = s.gpr r) →
      (∀ r ∈ calleeSaved, r ≠ .rsp → s₃.gpr r = s.gpr r) → s₃.gpr .rsp = F s → s₃.gpr .r11 = S s →
      s₃.rd = s.rd → s₃.wr = fR s :: s.wr → Kept s 0 s₃.mem → Frame [fR s] s.mem s₃.mem → Post s₃ s₄ →
      Mid s (n s - n s % 16) 0 (ys (n s - n s % 16)) s₄)
    {s₁ : State} (hsp : s₁.gpr .rsp = F s) (h11 : s₁.gpr .r11 = S s) (hg : ∀ r, r ≠ .r11 → r ≠ .rsp → s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [fR s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = fR s :: s.wr) :
    WP isa (stitchPart piece) s₁ (Mid s (n s - n s % 16) 0 (ys (n s - n s % 16))) := by
  refine WP.seq (WP.mono (cmp16_ok (hg _ (by decide) (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  refine WP.ite (decide (n s < 16)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · have h0 : n s - n s % 16 = 0 := by simp at h; omega
    rw [h0, hys]
    refine WP.block_nil (mid_entry hp (by rw [g₂]; exact hsp) (fun r hr h' => by rw [g₂]; exact hg r hr h')
      (by rw [m₂]; exact hk) (by rw [m₂]; exact hf) (rd₂.trans hrd) (wr₂.trans hwr))
  · have h16 : 16 ≤ n s := by simp at h; omega
    refine WP.seq (WP.mono (split_ok (s := s) (by rw [g₂]; exact hg _ (by decide) (by decide)))
      fun s₃ ⟨h9, g₃, m₃, rd₃, wr₃⟩ => ?_)
    have ga : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r := fun r hr => by
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [g₃ r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), g₂,
        hg r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
          (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    have gc : ∀ r ∈ calleeSaved, r ≠ .rsp → s₃.gpr r = s.gpr r := fun r hr h' => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [g₃ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), g₂,
        hg r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) h']
    have gsp : s₃.gpr .rsp = F s := by rw [g₃ _ (by decide) (by decide), g₂, hsp]
    have g11 : s₃.gpr .r11 = S s := by rw [g₃ _ (by decide) (by decide), g₂, h11]
    have rd₃' : s₃.rd = s.rd := rd₃.trans (rd₂.trans hrd)
    have wr₃' : s₃.wr = fR s :: s.wr := wr₃.trans (wr₂.trans hwr)
    have hk₃ : Kept s 0 s₃.mem := by rw [m₃, m₂]; exact hk
    have hf₃ : Frame [fR s] s.mem s₃.mem := by rw [m₃, m₂]; exact hf
    exact WP.mono (hpiece s₃ (spre_of hp h16 h9 ga g11 rd₃' wr₃')) fun s₄ hP =>
      hpost s₃ s₄ h9 ga gc gsp g11 rd₃' wr₃' hk₃ hf₃ hP

/-- Encryption: the blocks hashed are those written. -/
theorem stitchE_ok {s₁ : State} (hsp : s₁.gpr .rsp = F s) (h11 : s₁.gpr .r11 = S s)
    (hg : ∀ r, r ≠ .r11 → r ≠ .rsp → s₁.gpr r = s.gpr r) (hk : Kept s 0 s₁.mem) (hf : Frame [fR s] s.mem s₁.mem)
    (hrd : s₁.rd = s.rd) (hwr : s₁.wr = fR s :: s.wr) :
    WP isa (stitchPart Impl.Gcm.X86_64.Stitch.enc) s₁
      (Mid s (n s - n s % 16) 0
        (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (n s - n s % 16)))) :=
  stitch_ok hp (ys := fun q => ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)) rfl
    (fun _ h => Gcm.X86_64.Stitch.enc_ok h)
    (fun s₃ s₄ h9 ga gc gsp g11 rd₃ wr₃ hk₃ hf₃ hP => by
      refine mid_of_post hp h9 ga gc gsp g11 rd₃ wr₃ hk₃ hf₃ hP.data hP.ctr hP.frame hP.gpr hP.rd hP.wr
        fun eH eY _ eD => ?_
      have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
      have hy := hP.y
      simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
        Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.nb, h9, ga _ (by simp [argRegs] : Reg.rcx ∈ argRegs),
        ga _ (by simp [argRegs] : Reg.rdi ∈ argRegs), ga _ (by simp [argRegs] : Reg.r8 ∈ argRegs),
        toNat_ofNat_of_lt (show n s - n s % 16 < 2 ^ 64 by omega)] at hy
      rw [hy, eH, eY, eD])
    hsp h11 hg hk hf hrd hwr

/-- Decryption: the blocks hashed are those read. -/
theorem stitchD_ok {s₁ : State} (hsp : s₁.gpr .rsp = F s) (h11 : s₁.gpr .r11 = S s)
    (hg : ∀ r, r ≠ .r11 → r ≠ .rsp → s₁.gpr r = s.gpr r) (hk : Kept s 0 s₁.mem) (hf : Frame [fR s] s.mem s₁.mem)
    (hrd : s₁.rd = s.rd) (hwr : s₁.wr = fR s :: s.wr) :
    WP isa (stitchPart Impl.Gcm.X86_64.Stitch.dec) s₁
      (Mid s (n s - n s % 16) 0
        (blocksAt s.mem (D s) (n s - n s % 16))) :=
  stitch_ok hp (ys := fun q => blocksAt s.mem (D s) q) rfl
    (fun _ h => Gcm.X86_64.Stitch.dec_ok h)
    (fun s₃ s₄ h9 ga gc gsp g11 rd₃ wr₃ hk₃ hf₃ hP => by
      refine mid_of_post hp h9 ga gc gsp g11 rd₃ wr₃ hk₃ hf₃ hP.data hP.ctr hP.frame hP.gpr hP.rd hP.wr
        fun eH eY eD _ => ?_
      have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
      have hy := hP.y
      simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
        Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.nb, h9, ga _ (by simp [argRegs] : Reg.rcx ∈ argRegs),
        ga _ (by simp [argRegs] : Reg.rdi ∈ argRegs), ga _ (by simp [argRegs] : Reg.r8 ∈ argRegs),
        toNat_ofNat_of_lt (show n s - n s % 16 < 2 ^ 64 by omega)] at hy
      rw [hy, eH, eY, eD])
    hsp h11 hg hk hf hrd hwr

end

end VG.Proof.AesGcm.X86_64.Blocks
