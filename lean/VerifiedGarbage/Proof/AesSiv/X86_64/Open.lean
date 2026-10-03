import VerifiedGarbage.Proof.AesSiv.X86_64.Seal

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 succ_ofNat bytesAt_succ)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-- The OR of the XORs of the halves of the IVs at `W` and `W + 112` is 0
exactly if they are equal. -/
theorem ivs_eq (m : Mem) (W : Addr) :
    ((m.readW W 64 ^^^ m.readW (W + BitVec.ofNat 64 tOff) 64) |||
        (m.readW (W + BitVec.ofNat 64 8) 64 ^^^ m.readW (W + BitVec.ofNat 64 (tOff + 8)) 64)) = 0 ↔
      Spec.Aes.bytesAt m W 16 = Spec.Aes.bytesAt m (W + BitVec.ofNat 64 tOff) 16 := by
  rw [or_xor_eq_zero, Proof.Cmac.bytesAt_split, Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, le8_append_eq, Offset.add_add]

theorem compare_ok (h : Env s₀ C D P W R L) {s : State} (h15 : s.gpr .r15 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa compare s = some s' ∧
      s'.gpr .rax = (if Spec.Aes.bytesAt s.mem W 16 = Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 tOff) 16
        then 1 else 0) ∧
      s'.gpr .r11 = 0 - s'.gpr .rax ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 dbOff) (s'.gpr .rax) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := h.inRW hrd hwr (d := 0) (n := 8) (by decide)
  have r₁ := h.inRW hrd hwr (d := tOff) (n := 8) (by decide)
  have r₂ := h.inRW hrd hwr (d := 8) (n := 8) (by decide)
  have r₃ := h.inRW hrd hwr (d := tOff + 8) (n := 8) (by decide)
  have w₀ := h.inW hwr (d := dbOff) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.AesSiv.X86_64.compare, imm, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, readSrc32, execAlu, execShift, State.load64, State.store64, State.ea,
      State.setReg32, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg,
      mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, gpr_setFlags, mem_setFlags, rd_setFlags,
      wr_setFlags, ite_true, ite_false, h15, r₀, r₁, r₂, r₃, w₀]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false]
    rw [show (1#32 : BitVec 32) = 1 from rfl, eqz, k0]
    simp only [ivs_eq]
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false]
    rfl
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_setReg, gpr_setFlags, h₁, h₂, h₃, h₄]
  all_goals rfl

/-! ## Masking the data -/

theorem maskStep_ok (s : State) {P : Addr} {j L : Nat} {c : Bool} (h13 : s.gpr .r13 = P)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 L)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 1) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax maskByte, .alu .and .rax (.reg .r11), .store8 maskByte .rax,
        .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .r14)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j) ((if c then s.mem (P + BitVec.ofNat 64 j) else 0 : Byte)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 j + 1 ∧
      s'.zf = some (BitVec.ofNat 64 j + 1 - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea : s.gpr .r13 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 j := by
    rw [h13, h10, BitVec.mul_one]; simp
  refine ⟨_, by
    simp (config := {decide := true}) only [maskByte, imm, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true,
      ite_false, ea, rq, wq]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, h11, mask_byte]
  · simp [gpr_setReg, h10]
  · simp [h10, h14]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- What `maskData` leaves: the data, or zeros. -/
structure Masked (s : State) (P : Addr) (L : Nat) (c : Bool) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P L else Spec.Siv.zeros L)
  other : ∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then Spec.Aes.bytesAt m P j else Spec.Siv.zeros j).length = j := by
  cases c <;> simp [Spec.Siv.zeros, Proof.Cmac.bytesAt_length]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then Spec.Aes.bytesAt m P (j + 1) else Spec.Siv.zeros (j + 1)) =
      (if c then Spec.Aes.bytesAt m P j else Spec.Siv.zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [Spec.Siv.zeros, bytesAt_succ, List.replicate_succ']

theorem maskData_wp (s : State) {P : Addr} {L : Nat} {c : Bool} (hL : L < 2 ^ 64) (h13 : s.gpr .r13 = P)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (h11 : s.gpr .r11 = 0 - (if c then 1 else 0))
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (P + BitVec.ofNat 64 i) 1) :
    WP isa maskData s (Masked s P L c) := by
  obtain ⟨s₁, run₁, r10₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (.imm 0),
      .alu .test .r14 (.reg .r14)] s = some s₁ ∧ s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁.zf = some (decide (L = 0)) ∧
      (∀ r, r ≠ .r10 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.setReg32,
        Option.map_some, Option.bind_some]
      rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · rw [zf_arithFlags]
      simp (config := {decide := true}) only [gpr_setReg, ite_false]
      rw [h14, BitVec.and_self, Proof.CmacAes.Stream.X86_64.beq_zero_iff, toNat_ofNat hL]
    · intro r h; simp [gpr_setReg, h]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (L = 0)) zf₁ (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hL0 : L = 0 := of_decide_eq_true hb
    subst hL0
    refine ⟨?_, fun r _ h => g₁ r h, rd₁, wr₁⟩
    rw [m₁]
    cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, writeBytes_nil]
  have hL0 : 0 < L := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = L - j ∧ j < L ∧ t.gpr .r10 = BitVec.ofNat 64 j ∧
      t.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P j else Spec.Siv.zeros j) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL0, r10₁, by rw [m₁]; cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, writeBytes_nil],
      fun r _ h => g₁ r h, rd₁, wr₁⟩
  rintro k t ⟨j, rfl, hj, r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := maskStep_ok t (P := P) (j := j) (L := L) (c := c)
    (by rw [g _ (by decide) (by decide), h13]) r10 (by rw [g _ (by decide) (by decide), h11])
    (by rw [g _ (by decide) (by decide), h14]) (by rw [rd, wr]; exact hr j hj) (by rw [wr]; exact hw j hj)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨P, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (P + BitVec.ofNat 64 j) = s.mem (P + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat P (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P (j + 1) else Spec.Siv.zeros (j + 1)) := by
    rw [mem', hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have hz : t'.zf = some (decide (j + 1 = L)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : j + 1 = L
  · left
    exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], L - (j + 1), by omega, j + 1, rfl, by omega, by rw [r10', succ_ofNat], hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The whole function -/

/-- The save writes only the slots, at `W + 160` to `W + 224`. -/
theorem cryptMem_frame' : Frame [⟨W + BitVec.ofNat 64 160, 64⟩] s₀.mem (cryptMem s₀ P W L) :=
  ((Spill.saveMem_frame _ _ _ _ fun p hp => Offset.contains W (saved_ge p hp) (by have := saved_le p hp; omega)
      (by decide)).writeW (List.mem_singleton_self _) _ (Offset.contains W (by decide) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains W (by decide) (by decide) (by decide))

theorem open_wp (v : Ctr32Impl) {s₀ : State} (h0 : openX86_64.pre s₀) :
    WP isa («open» v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ openX86_64.post s₀ s' := by
  have h := Env.ofCrypt h0
  have ha := ArgRegs.ofCrypt h0
  have hcp := cryptPre_cp h0
  have hPw := cryptPre_pw h0
  show WP isa _ s₀ fun s' => gprPreserved s₀ s' ∧
    match Spec.Siv.openWith (Spec.Siv.ctxMac s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)
        (Spec.Siv.ctxCiph s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdx) 16)
        (Spec.Aes.bytesAt s₀.mem (s₀.gpr .r9) 16) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat) with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.Aes.bytesAt s'.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat = Spec.Siv.zeros (s₀.gpr .r8).toNat
  generalize s₀.gpr .rdi = C at h ha hcp ⊢
  generalize s₀.gpr .rdx = D at h ha ⊢
  generalize s₀.gpr .rcx = P at h ha hcp hPw ⊢
  generalize s₀.gpr .r9 = W at h ha ⊢
  generalize (s₀.gpr .rsi).toNat = R at h ha ⊢
  generalize (s₀.gpr .r8).toNat = L at h ha hcp hPw ⊢
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have hL : L ≤ 2 ^ 64 := by have := h.lt; omega
  -- The save and the counter.
  obtain ⟨s₁', run₁', hr₁', m₁'⟩ := cryptPre_ok h ha
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := counter_ok h hr₁'.r15 hr₁'.rd hr₁'.wr
  have hr₁ : Regs s₀ C D P W R L s₁ := hr₁'.keep (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) rd₁ wr₁
  have f₁ : Frame [⟨W, 2560⟩] s₀.mem s₁'.mem := m₁' ▸ cryptMem_frame h
  have fc : Frame (cntRegions W) s₁'.mem s₁.mem := m₁ ▸ counter_frame _ _ _ _
  refine WP.seq (WP.of_runBlock ⟨s₁, by rw [runBlock_append, run₁', Option.bind_some, run₁], ?_⟩)
  have hslot {d : Nat} (hd : 208 ≤ d) (hd' : d + 8 ≤ 224) :
      s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁'.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fc.readW (Region.contains_self _ _) (cnt_dis (by omega) (by omega)) (by decide)
  have h208 : s₁.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P := by
    rw [hslot (by decide) (by decide), m₁', cryptMem_data]
  have h216 : s₁.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L := by
    rw [hslot (by decide) (by decide), m₁', cryptMem_len]
  have hcnt : ∃ hi lo : BitVec 64, s₁.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
      s₁.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt s₁'.mem W 16)) := by
    rw [m₁]; exact counter_cnt s₁'.mem W
  -- CTR.
  refine WP.seq (WP.mono (ctr_wp v h hcp hPw hr₁ hcnt h208 h216) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  -- S2V into `W + 112`.
  refine WP.seq (WP.mono (finish_wp v h h₂.regs (out := tOff) (Or.inr rfl)) fun s₃ h₃ => ?_)
  have f₃ := h₃.frame
  -- The comparison.
  obtain ⟨s₄, run₄, rax₄, r11₄, m₄, g₄, rd₄, wr₄⟩ := compare_ok h h₃.regs.r15 h₃.regs.rd h₃.regs.wr
  have hr₄ : Regs s₀ C D P W R L s₄ := h₃.regs.keep (fun r hr => g₄ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide))
    rd₄ wr₄
  have f₄ : Frame [⟨W + BitVec.ofNat 64 dbOff, 8⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  -- The mask.
  refine WP.seq (WP.mono (maskData_wp s₄ (c := decide (Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16)) h.lt hr₄.r13 hr₄.r14
    (by rw [r11₄, rax₄]; simp only [decide_eq_true_eq]) (fun i hi => h.inRP hr₄.rd hr₄.wr (by omega))
    (fun i hi => h.inWP hPw hr₄.wr (by omega))) fun s₅ h₅ => ?_)
  have f₅ : Frame [⟨P, L⟩] s₄.mem s₅.mem := by
    rw [h₅.mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  -- The result, then the restore.
  have dP144 := h.p_w.sub_right (h.sW (d := dbOff) (n := 8) (by decide))
  have r144 : s₅.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = s₄.gpr .rax := by
    rw [f₅.readW (Region.contains_self _ _) (one_out dP144.symm) (by decide), m₄, Mem.readW_writeW_self64]
  have hr₅ : Regs s₀ C D P W R L s₅ := hr₄.keep (fun r hr => h₅.other r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) h₅.rd h₅.wr
  have run₆ : runBlock isa [.mov .rax (.mem (at_ .r15 dbOff))] s₅ =
      some (s₅.setReg .rax (s₄.gpr .rax)) := by
    have r := h.inRW hr₅.rd hr₅.wr (d := dbOff) (n := 8) (by decide)
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, hr₅.r15, r, ite_true, r144]
  have hsv : Spill.Saved (s₅.setReg .rax (s₄.gpr .rax)).mem W s₀.gpr saved := by
    have hb (p : Reg × Nat) (hp : p ∈ saved) : 160 ≤ p.2 ∧ p.2 + 8 ≤ 208 := ⟨saved_ge p hp, saved_le p hp⟩
    rw [mem_setReg]
    refine (((((m₁' ▸ cryptMem_saved).frame fc fun p hp => ?_).frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame
      f₄ fun p hp => ?_).frame f₅ fun p hp => ?_
    · have := hb p hp; exact cnt_dis (by omega) (by omega)
    · have := hb p hp; exact ctr_dis h (by omega) (by omega)
    · have := hb p hp
      exact fin_dis h (by decide) (by omega) (by simp only [tOff]; omega) (by omega) (by omega) (by omega) (by omega)
    · have := hb p hp
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (by simp only [dbOff]; omega) (by omega) (by decide)
    · have := hb p hp
      exact one_out (h.p_w.sub_right (h.sW (d := p.2) (n := 8) (by omega))).symm
  rw [show [.mov .rax (.mem (at_ .r15 dbOff))] ++ restore =
    ([.mov .rax (.mem (at_ .r15 dbOff))] : List Instr) ++ restoreCode .r15 saved from rfl]
  refine WP.block_append (WP.of_runBlock ⟨_, run₆, ?_⟩)
  refine WP.mono (Spill.restore_ok .r15 saved s₀.gpr _ (by decide) (fun p hp => by
      rw [gpr_setReg_of_ne _ _ (by decide), hr₅.r15, rd_setReg, wr_setReg, hr₅.rd, hr₅.wr]
      exact h.inRW rfl rfl (by have := saved_le p hp; omega))
    (by rw [gpr_setReg_of_ne _ _ (by decide), hr₅.r15]; exact hsv)) fun s₇ ⟨h₇a, h₇b, m₇, _, _⟩ => ?_
  have rax₇ : s₇.gpr .rax = s₄.gpr .rax := by rw [h₇b _ (by decide), gpr_setReg_self]
  have mem₇ : s₇.mem = s₅.mem := by rw [m₇, mem_setReg]
  -- The IV, the plaintext and S2V's end, from the arguments.
  have hV : Spec.Aes.bytesAt s₃.mem W 16 = Spec.Aes.bytesAt s₀.mem W 16 := by
    have d₃ := fin_dis h (out := tOff) (d := 0) (n := 16) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    have d₂ := ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
    have dc := cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
    rw [k0] at d₃ d₂ dc
    rw [bytesAt_frame f₃ d₃ (by decide), bytesAt_frame f₂ d₂ (by decide), bytesAt_frame fc dc (by decide), m₁',
      bytesAt_frame cryptMem_frame' (one_out (Offset.disjoint_base W (d := 160) (n := 64) (k := 16) (by decide)
        (by decide)).symm) (by decide)]
  have hq : Spec.Aes.bytesAt s₁'.mem W 16 = Spec.Aes.bytesAt s₀.mem W 16 := by
    rw [m₁', bytesAt_frame cryptMem_frame' (one_out (Offset.disjoint_base W (d := 160) (n := 64) (k := 16) (by decide)
        (by decide)).symm) (by decide)]
  have hp : Spec.Aes.bytesAt s₂.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph s₀.mem C R)
      (Spec.Siv.counter (Spec.Aes.bytesAt s₀.mem W 16)) (Spec.Aes.bytesAt s₀.mem P L) := by
    rw [h₂.data, hq, ctxCiph_frame fc (cnt_out h.c_w) hRb, ctxCiph_frame f₁ (one_out h.c_w) hRb,
      bytesAt_frame fc (cnt_out h.p_w) hL, bytesAt_frame f₁ (one_out h.p_w) hL]
  have hT : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s₀.mem C R) (Spec.Aes.bytesAt s₀.mem D 16)
        (Spec.Siv.ctr (Spec.Siv.ctxCiph s₀.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s₀.mem W 16))
          (Spec.Aes.bytesAt s₀.mem P L)) := by
    rw [h₃.out, hp, ctxMac_frame f₂ (ctr_out hcp h.c_w h.stk_c) hRb, ctxMac_frame fc (cnt_out h.c_w) hRb,
      ctxMac_frame f₁ (one_out h.c_w) hRb, bytesAt_frame f₂ (ctr_out h.d_p h.d_w h.stk_d) (by decide),
      bytesAt_frame fc (cnt_out h.d_w) (by decide), bytesAt_frame f₁ (one_out h.d_w) (by decide)]
  have hd : Spec.Aes.bytesAt s₇.mem P L = if Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16 then
        Spec.Siv.ctr (Spec.Siv.ctxCiph s₀.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s₀.mem W 16))
          (Spec.Aes.bytesAt s₀.mem P L) else Spec.Siv.zeros L := by
    have hl := length_mask s₄.mem P (decide (Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16)) L
    have hw := VG.Proof.CmacAes.Stream.X86_64.bytesAt_writeBytes_self s₄.mem P (by rw [hl]; exact h.lt)
    rw [hl] at hw
    rw [mem₇, h₅.mem, hw, bytesAt_frame f₄ (one_out dP144) hL, bytesAt_frame f₃ (fin_out (by decide) h.p_w h.stk_p) hL, hp]
    simp only [decide_eq_true_eq]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hsp : r = .rsp
    · subst hsp; rw [h₇b _ (by decide), gpr_setReg_of_ne _ _ (by decide), hr₅.rsp]
    · exact h₇a r (saved_all r hr hsp)
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    have hw := h.ret_w
    have hb := Offset.base_disjoint_below (s₀.gpr .rsp) (n := 16) (k := 8) (by decide)
    rw [mem₇, f₅.readW c (one_out h.ret_p) (by decide),
      f₄.readW c (one_out (hw.sub_right (h.sW (by decide)))) (by decide),
      f₃.readW c (fin_out (by decide) hw hb.symm) (by decide), f₂.readW c (ctr_out h.ret_p hw hb.symm) (by decide),
      fc.readW c (cnt_out hw) (by decide), f₁.readW c (one_out hw) (by decide)]
  · rw [rax₇, rax₄, hd, hV, hT]
    simp only [Spec.Siv.openWith]
    by_cases hc : Spec.Siv.s2vFinish (Spec.Siv.ctxMac s₀.mem C R) (Spec.Aes.bytesAt s₀.mem D 16)
        (Spec.Siv.ctr (Spec.Siv.ctxCiph s₀.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s₀.mem W 16))
          (Spec.Aes.bytesAt s₀.mem P L)) = Spec.Aes.bytesAt s₀.mem W 16
    · rw [ite_eq_left hc, ite_eq_left hc.symm, ite_eq_left hc.symm]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hc, ite_eq_right (Ne.symm hc), ite_eq_right (Ne.symm hc)]
      exact ⟨rfl, rfl⟩

end VG.Proof.AesSiv.X86_64
