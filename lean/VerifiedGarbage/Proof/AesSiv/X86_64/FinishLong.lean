import VerifiedGarbage.Proof.AesSiv.X86_64.FinishShort

/-!
# AES-SIV on x86-64: finishing S2V with a string of a block or more

For a last string `P` of `L ≥ 16` bytes, with `nb = ⌊(L − 1) / 16⌋` whole
blocks before its last 1 to 16 bytes, `k = max(nb, 1) − 1` (`kOf`) and
`j = min(nb, 1)` (`jOf`): `longTail` copies the last `T = L − 16 k` bytes of
`P` (17 to 32 of them, or 16 if `L = 16`) to the tail at `W + 32` and XORs
`D` into its last 16 bytes, so the tail is `P[16k..] xorend D`; `longMac`
chains the `k` blocks of `P`, then the first `j` blocks of the tail, and
finalizes the rest of the tail (`Siv.s2vFinish_long`, `Siv.cmacWith_split₂`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes frame_store2 mn xor2Mem xor2_ok
  xor2Mem_bytes xor2Mem_frame)
open VG.Proof.CmacAes.Stream.X86_64 (UArgs FArgs Copied copy_ok toNat_ofNat toNat_add_lt upd_call
  bytesAt_writeBytes_self)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## The lengths -/

/-- The whole blocks of `P` chained before the tail. -/
def kOf (L : Nat) : Nat := if L < 17 then 0 else (L - 1) / 16 - 1

/-- The whole blocks of the tail chained before its last bytes. -/
def jOf (L : Nat) : Nat := if L < 17 then 0 else 1

theorem kOf_lt {L : Nat} (h : L < 17) : kOf L = 0 := by simp [kOf, h]

theorem kOf_ge {L : Nat} (h : ¬ L < 17) : kOf L = (L - 1) / 16 - 1 := by simp [kOf, h]

theorem kOf_tail {L : Nat} (h : 16 ≤ L) : 16 ≤ L - 16 * kOf L ∧ L - 16 * kOf L ≤ 32 := by
  unfold kOf; split <;> omega

theorem jOf_rest {L : Nat} (h : 16 ≤ L) :
    16 * jOf L ≤ L - 16 * kOf L ∧ 0 < L - 16 * kOf L - 16 * jOf L ∧ L - 16 * kOf L - 16 * jOf L ≤ 16 := by
  unfold kOf jOf; split <;> omega

/-- Four doublings, as `add rax, rax` computes them. -/
theorem dbl4 (x : Nat) (_h : 16 * x < 2 ^ 64) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 x + (BitVec.ofNat 64 x + BitVec.ofNat 64 x) +
        (BitVec.ofNat 64 x + BitVec.ofNat 64 x + (BitVec.ofNat 64 x + BitVec.ofNat 64 x)) +
      (BitVec.ofNat 64 x + BitVec.ofNat 64 x + (BitVec.ofNat 64 x + BitVec.ofNat 64 x) +
        (BitVec.ofNat 64 x + BitVec.ofNat 64 x + (BitVec.ofNat 64 x + BitVec.ofNat 64 x))) =
      BitVec.ofNat 64 (16 * x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `16 k`, as the code computes it for `L ≥ 17`: `((L − 1) >> 4) − 1`, doubled four times. -/
theorem kOf_bv {L : Nat} (h : 17 ≤ L) (hL : L < 2 ^ 64) :
    (BitVec.ofNat 64 L - BitVec.signExtend 64 (BitVec.ofNat 32 1)) >>> 4 - BitVec.signExtend 64 (BitVec.ofNat 32 1) =
      BitVec.ofNat 64 (kOf L) := by
  rw [sx_ofNat (by decide)]
  unfold kOf
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by omega))]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-! ## The tail -/

/-- XORing `D` into the last 16 of `T` bytes. -/
theorem xorend_mem (m : Mem) {B Q : Addr} {T : Nat} (hT : 16 ≤ T) (hw : B.toNat + T ≤ 2 ^ 64)
    (hd : (⟨B, T⟩ : Region).Disjoint ⟨Q, 16⟩) :
    Spec.Aes.bytesAt (xor2Mem m (B + BitVec.ofNat 64 (T - 16)) (B + BitVec.ofNat 64 (T - 16)) Q) B T =
      Spec.Siv.xorend (Spec.Aes.bytesAt m B T) (Spec.Aes.bytesAt m Q 16) := by
  have hc : Region.Sub ⟨B + BitVec.ofNat 64 (T - 16), 16⟩ ⟨B, T⟩ := Offset.sub_base B (by omega)
  have e : T = (T - 16) + 16 := by omega
  have hs := Proof.Cmac.Stream.bytesAt_append (xor2Mem m (B + BitVec.ofNat 64 (T - 16))
    (B + BitVec.ofNat 64 (T - 16)) Q) B (T - 16) 16
  rw [← e] at hs
  rw [hs, Spec.Siv.xorend, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]
  have tk := take_bytesAt m B (a := T - 16) (b := 16)
  have dr := drop_bytesAt m B (a := T - 16) (b := 16)
  rw [← e] at tk dr
  rw [tk, dr, bytesAt_frame (xor2Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint B (by omega) (by omega)) (by omega),
    xor2Mem_bytes _ ?_ ?_, Siv.xor_eq]
  · rw [Offset.add_add]; exact Offset.disjoint B (by omega) (by omega) (by omega)
  · exact (hd.sub_left (fun a ha => hc a (Region.sub_prefix (base := B + BitVec.ofNat 64 (T - 16)) (len := 8)
      (len' := 16) (by decide) a ha))).sub_right (Offset.sub_base Q (d := 8) (n := 8) (k := 16) (by decide))

theorem cmp17_ok {s : State} (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (hL : L < 2 ^ 64) :
    ∃ s', runBlock isa [.alu .cmp .r14 (imm 17)] s = some s' ∧ s'.cf = some (decide (L < 17)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cf_arithFlags, h14, sx_ofNat (by decide), toNat_ofNat hL, toNat_ofNat (by decide)]
  all_goals rfl

/-- `16 k` in `rax`. -/
theorem kBranch_wp {s : State} (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (hL16 : 16 ≤ L) (hL : L < 2 ^ 64)
    (hcf : s.cf = some (decide (L < 17))) :
    WP isa (.ite .b (.block [.mov32 .rax (.imm 0)])
        (.block [.mov .rcx (.reg .r14), .alu .sub .rcx (imm 1), .shift .shr .rcx 4,
          .alu .sub .rcx (imm 1), .mov .rax (.reg .rcx), .alu .add .rax (.reg .rax),
          .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax)])) s fun s' =>
      s'.gpr .rax = BitVec.ofNat 64 (16 * kOf L) ∧ (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.ite (decide (L < 17)) hcf (fun hb => ?_) (fun hb => ?_)
  · have h17 : L < 17 := of_decide_eq_true hb
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
      rfl, ?_⟩
    refine ⟨?_, fun r h₁ _ => gpr_setReg_of_ne _ _ h₁, rfl, rfl, rfl⟩
    rw [gpr_setReg_self, kOf_lt h17]
    rfl
  · have h17 : ¬ L < 17 := of_decide_eq_false hb
    refine WP.of_runBlock ⟨_, by
      simp only [imm, runBlock_cons, runStep_some, exec, readSrc, execAlu, execShift,
        Option.bind_some, Option.map_some]
      rfl, ?_⟩
    simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
      mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags,
      ite_true, ite_false, h14, kOf_bv (by omega) hL]
    refine ⟨dbl4 _ (by rw [kOf_ge h17]; omega), fun r h₁ h₂ => by simp [h₁, h₂], trivial⟩

theorem t1_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) {a : Nat}
    (hrax : s.gpr .rax = BitVec.ofNat 64 a) (ha : a ≤ L) :
    ∃ s', runBlock isa [.store (at_ .r15 dbOff) .rax, .alu .add .r13 (.reg .rax), .mov .rcx (.reg .r14),
        .alu .sub .rcx (.reg .rax), .mov .rdx (.reg .r15), .alu .add .rdx (imm tailOff)] s = some s' ∧
      s'.gpr .r13 = P + BitVec.ofNat 64 a ∧ s'.gpr .rcx = BitVec.ofNat 64 (L - a) ∧
      s'.gpr .rdx = W + BitVec.ofNat 64 32 ∧
      (∀ r, r ≠ .r13 → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 144) (BitVec.ofNat 64 a) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w := h.inW hr.wr (d := dbOff) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [imm, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      execAlu, State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      ite_true, ite_false, hr.r15, w]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, hr.r13, hr.r14, hrax,
    tailOff, sx_ofNat (show 32 < 2 ^ 31 by decide), Offset.ofNat_sub_ofNat ha]
  refine ⟨trivial, trivial, trivial, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], rfl, trivial⟩

theorem t2a_ok (h : Env s₀ C D P W R L) {s : State} {a : Nat} (ha : a ≤ L)
    (h13 : s.gpr .r13 = P + BitVec.ofNat 64 a) (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (h15 : s.gpr .r15 = W)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : s.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = BitVec.ofNat 64 a) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .r15 dbOff)), .alu .sub .r13 (.reg .rax), .mov .rcx (.reg .r14),
        .alu .sub .rcx (.reg .rax), .alu .add .rcx (.reg .r15)] s = some s' ∧
      s'.gpr .r13 = P ∧ s'.gpr .rcx = W + BitVec.ofNat 64 (L - a) ∧
      (∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r := h.inRW hrd hwr (d := dbOff) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      execAlu, State.load64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      ite_true, ite_false, h15, r]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, h13, h14, hm,
    Offset.ofNat_sub_ofNat ha, BitVec.add_sub_cancel]
  refine ⟨trivial, BitVec.add_comm _ _, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial⟩

/-- `D` XORed into the last block of the `T` tail bytes. -/
theorem t2b_ok (h : Env s₀ C D P W R L) {s : State} {T : Nat} (hT : 16 ≤ T) (hT32 : T ≤ 32)
    (hrcx : s.gpr .rcx = W + BitVec.ofNat 64 T) (h12 : s.gpr .r12 = D) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .rcx (tailOff - 16))), .alu .xor .rax (.mem (at_ .r12 0)),
        .store (at_ .rcx (tailOff - 16)) .rax, .mov .rax (.mem (at_ .rcx (tailOff - 8))),
        .alu .xor .rax (.mem (at_ .r12 8)), .store (at_ .rcx (tailOff - 8)) .rax] s = some s' ∧
      s'.mem = xor2Mem s.mem (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (T - 16))
        (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (T - 16)) D ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e : W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (T - 16) = W + BitVec.ofNat 64 (T + 16) := by
    rw [Offset.add_add, show 32 + (T - 16) = T + 16 by omega]
  have e8 : W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (T - 16) + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 (T + 24) := by
    rw [e, Offset.add_add]
  have i (d : Nat) (hd : d + 8 ≤ 64) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 :=
    h.inRW hrd hwr (by omega)
  obtain ⟨s', run, m, g, rd, wr⟩ := xor2_ok s .rcx .r12 .rcx (tailOff - 16) 0 (tailOff - 16)
    (P := W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (T - 16)) (Q := D)
    (C := W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (T - 16))
    (by rw [hrcx, e, Offset.add_add]; rfl) (by rw [hrcx, e8, Offset.add_add]; rfl)
    (by rw [h12, k0]) (by rw [h12])
    (by rw [hrcx, e, Offset.add_add]; rfl) (by rw [hrcx, e8, Offset.add_add]; rfl)
    ⟨by decide, by decide, by decide⟩
    (by rw [e]; exact i _ (by omega)) (by rw [e8]; exact i _ (by omega))
    (by have := h.inRD hrd hwr (d := 0) (n := 8) (by decide); rwa [k0] at this)
    (h.inRD hrd hwr (by decide))
    (by rw [e]; exact h.inW hwr (by omega)) (by rw [e8]; exact h.inW hwr (by omega))
  exact ⟨s', run, m, g, rd, wr⟩

/-- What `longTail` leaves: `16 k` at `W + 144`, and the tail
`P[16k..] xorend D` at `W + 32`. -/
structure LTail (s₀ : State) (C D P W : Addr) (R L : Nat) (s s' : State) : Prop where
  regs : Regs s₀ C D P W R L s'
  frame : Frame [⟨W + BitVec.ofNat 64 32, 32⟩, ⟨W + BitVec.ofNat 64 144, 8⟩] s.mem s'.mem
  a : s'.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (16 * kOf L)
  tail : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 32) (L - 16 * kOf L) =
    Spec.Siv.xorend (Spec.Aes.bytesAt s.mem (P + BitVec.ofNat 64 (16 * kOf L)) (L - 16 * kOf L))
      (Spec.Aes.bytesAt s.mem D 16)

theorem longTail_wp (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) (hL16 : 16 ≤ L) :
    WP isa longTail s (LTail s₀ C D P W R L s) := by
  have hwW := h.wW
  have hlt := h.lt
  have hT := kOf_tail hL16
  obtain ⟨s₁, run₁, cf₁, g₁, m₁, rd₁, wr₁⟩ := cmp17_ok hr.r14 hlt
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (kBranch_wp (by rw [g₁, hr.r14]) hL16 hlt cf₁) fun s₂ ⟨rax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have hr₂ : Regs s₀ C D P W R L s₂ := hr.keep (fun r hr' => by
    rw [g₂ r (by rintro rfl; simp [calleeSaved] at hr') (by rintro rfl; simp [calleeSaved] at hr'), g₁])
    (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  obtain ⟨s₃, run₃, r13₃, rcx₃, rdx₃, g₃, m₃, rd₃, wr₃⟩ := t1_ok h hr₂ rax₂ (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, hr₂.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, hr₂.wr]
  have dPT : (⟨P + BitVec.ofNat 64 (16 * kOf L), L - 16 * kOf L⟩ : Region).Disjoint
      ⟨W + BitVec.ofNat 64 32, L - 16 * kOf L⟩ :=
    (h.p_w.sub_left (h.sP (by omega))).sub_right (h.sW (by omega))
  refine WP.seq (WP.mono (copy_ok s₃ (by omega) r13₃ rdx₃ rcx₃
    (fun i hi => by rw [Offset.add_add]; exact h.inRP rd₃' wr₃' (by omega))
    (fun i hi => by rw [Offset.add_add]; exact h.inW wr₃' (by omega)) dPT) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .r10) (h₃ : r ≠ .r13) (h₅ : r ≠ .rcx) (h₆ : r ≠ .rdx) :
      s₄.gpr r = s₂.gpr r := by rw [h₄.other r h₁ h₂, g₃ r h₃ h₅ h₆]
  have hlen : (Spec.Aes.bytesAt s₃.mem (P + BitVec.ofNat 64 (16 * kOf L)) (L - 16 * kOf L)).length =
      L - 16 * kOf L := Proof.Cmac.bytesAt_length _ _ _
  have f₄ : Frame [⟨W + BitVec.ofNat 64 32, 32⟩] s₃.mem s₄.mem := by
    rw [h₄.mem]; exact writeBytes_frame _ _ _ (by
      rw [hlen]; simpa using Offset.contains_base (W + BitVec.ofNat 64 32) (d := 0) (n := L - 16 * kOf L) (k := 32)
        (by omega) (by decide))
  have f₃ : Frame [⟨W + BitVec.ofNat 64 144, 8⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have a₄ : s₄.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (16 * kOf L) := by
    rw [f₄.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
        (by decide), m₃, Mem.readW_writeW_self64]
  obtain ⟨s₅, run₅, r13₅, rcx₅, g₅, m₅, rd₅, wr₅⟩ := t2a_ok h (a := 16 * kOf L) (by omega)
    (by rw [h₄.other _ (by decide) (by decide), r13₃])
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r14])
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r15])
    (by rw [h₄.rd, rd₃']) (by rw [h₄.wr, wr₃']) a₄
  obtain ⟨s₆, run₆, m₆, g₆, rd₆, wr₆⟩ := t2b_ok h hT.1 hT.2 rcx₅
    (by rw [g₅ _ (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide)
      (by decide), hr₂.r12]) (by rw [rd₅, h₄.rd, rd₃']) (by rw [wr₅, h₄.wr, wr₃'])
  refine WP.of_runBlock ⟨s₆, by
    rw [show ([.mov .rax (.mem (at_ .r15 dbOff)), .alu .sub .r13 (.reg .rax), .mov .rcx (.reg .r14),
        .alu .sub .rcx (.reg .rax), .alu .add .rcx (.reg .r15),
        .mov .rax (.mem (at_ .rcx (tailOff - 16))), .alu .xor .rax (.mem (at_ .r12 0)),
        .store (at_ .rcx (tailOff - 16)) .rax, .mov .rax (.mem (at_ .rcx (tailOff - 8))),
        .alu .xor .rax (.mem (at_ .r12 8)), .store (at_ .rcx (tailOff - 8)) .rax] : List Instr) =
        [.mov .rax (.mem (at_ .r15 dbOff)), .alu .sub .r13 (.reg .rax), .mov .rcx (.reg .r14),
        .alu .sub .rcx (.reg .rax), .alu .add .rcx (.reg .r15)] ++
        [.mov .rax (.mem (at_ .rcx (tailOff - 16))), .alu .xor .rax (.mem (at_ .r12 0)),
        .store (at_ .rcx (tailOff - 16)) .rax, .mov .rax (.mem (at_ .rcx (tailOff - 8))),
        .alu .xor .rax (.mem (at_ .r12 8)), .store (at_ .rcx (tailOff - 8)) .rax] from rfl,
      runBlock_append, run₅, Option.bind_some, run₆], ?_⟩
  have keep (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .r10) (h₃ : r ≠ .r13) (h₅ : r ≠ .rcx) (h₆ : r ≠ .rdx) :
      s₆.gpr r = s₂.gpr r := by rw [g₆ r h₁, g₅ r h₁ h₃ h₅, g₄ r h₁ h₂ h₃ h₅ h₆]
  have f₆ : Frame [⟨W + BitVec.ofNat 64 32, 32⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact (xor2Mem_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W + BitVec.ofNat 64 32, 32⟩, List.mem_singleton_self _,
        Offset.sub_base (W + BitVec.ofNat 64 32) (d := L - 16 * kOf L - 16) (n := 16) (k := 32) (by omega)⟩
  refine ⟨⟨by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rbx],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rbp],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r12],
      by rw [g₆ _ (by decide), r13₅],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r14],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r15],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rsp],
      by rw [rd₆, rd₅, h₄.rd, rd₃'], by rw [wr₆, wr₅, h₄.wr, wr₃']⟩, ?_, ?_, ?_⟩
  · have e₂ : s₂.mem = s.mem := by rw [m₂, m₁]
    rw [← e₂]
    exact ((f₃.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans
      (f₄.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)).trans
      (by rw [← m₅]; exact f₆.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  · rw [f₆.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
        (by decide), m₅, a₄]
  · have dD (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 32, 32⟩ : Region)]) : (⟨D, 16⟩ : Region).Disjoint r := by
      simp only [List.mem_singleton] at hr; subst hr; exact h.d_w.sub_right (h.sW (by decide))
    have tD : (⟨W + BitVec.ofNat 64 32, L - 16 * kOf L⟩ : Region).Disjoint ⟨D, 16⟩ :=
      (h.d_w.sub_right (h.sW (by omega))).symm
    have ws := bytesAt_writeBytes_self s₃.mem (W + BitVec.ofNat 64 32)
      (xs := Spec.Aes.bytesAt s₃.mem (P + BitVec.ofNat 64 (16 * kOf L)) (L - 16 * kOf L)) (by rw [hlen]; omega)
    rw [hlen] at ws
    rw [m₆, xorend_mem _ hT.1 (by rw [toNat_add_lt W hwW (show 32 < 2560 by decide)]; omega) tD, m₅, bytesAt_frame f₄ dD (by decide),
      h₄.mem, ws,
      bytesAt_frame f₃ (p := D) (n := 16) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.d_w.sub_right (h.sW (by decide))) (by decide),
      bytesAt_frame f₃ (p := P + BitVec.ofNat 64 (16 * kOf L)) (n := L - 16 * kOf L) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.p_w.sub_left (h.sP (by omega))).sub_right (h.sW (by decide))) (by omega), m₂, m₁]

end VG.Proof.AesSiv.X86_64
