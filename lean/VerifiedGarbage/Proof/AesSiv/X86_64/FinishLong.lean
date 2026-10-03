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
        .alu .sub .rcx (.reg .rax), .mov .rdx (.reg .r15), .alu .add .rdx (imm tailOff), .mov .r11 (.reg .rax)] s =
        some s' ∧
      s'.gpr .r13 = P + BitVec.ofNat 64 a ∧ s'.gpr .rcx = BitVec.ofNat 64 (L - a) ∧
      s'.gpr .rdx = W + BitVec.ofNat 64 32 ∧ s'.gpr .r11 = BitVec.ofNat 64 a ∧
      (∀ r, r ≠ .r13 → r ≠ .rcx → r ≠ .rdx → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
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
  refine ⟨trivial, trivial, trivial, trivial, fun r h₁ h₂ h₃ h₄ => by simp [h₁, h₂, h₃, h₄], rfl, trivial⟩

theorem t2a_ok {s : State} {a : Nat} (ha : a ≤ L)
    (h13 : s.gpr .r13 = P + BitVec.ofNat 64 a) (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (h15 : s.gpr .r15 = W)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 a) :
    ∃ s', runBlock isa [.alu .sub .r13 (.reg .r11), .mov .rcx (.reg .r14),
        .alu .sub .rcx (.reg .r11), .alu .add .rcx (.reg .r15)] s = some s' ∧
      s'.gpr .r13 = P ∧ s'.gpr .rcx = W + BitVec.ofNat 64 (L - a) ∧
      (∀ r, r ≠ .r13 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some, Option.map_some]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, h11, h13, h14, h15,
    Offset.ofNat_sub_ofNat ha, BitVec.add_sub_cancel]
  refine ⟨trivial, BitVec.add_comm _ _, fun r h₁ h₂ => by simp [h₁, h₂], trivial⟩

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
  obtain ⟨s₃, run₃, r13₃, rcx₃, rdx₃, r11₃, g₃, m₃, rd₃, wr₃⟩ := t1_ok h hr₂ rax₂ (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, hr₂.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, hr₂.wr]
  have dPT : (⟨P + BitVec.ofNat 64 (16 * kOf L), L - 16 * kOf L⟩ : Region).Disjoint
      ⟨W + BitVec.ofNat 64 32, L - 16 * kOf L⟩ :=
    (h.p_w.sub_left (h.sP (by omega))).sub_right (h.sW (by omega))
  refine WP.seq (WP.mono (copy_ok s₃ (by omega) r13₃ rdx₃ rcx₃
    (fun i hi => by rw [Offset.add_add]; exact h.inRP rd₃' wr₃' (by omega))
    (fun i hi => by rw [Offset.add_add]; exact h.inW wr₃' (by omega)) dPT) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .r10) (h₃ : r ≠ .r13) (h₅ : r ≠ .rcx) (h₆ : r ≠ .rdx)
      (h₇ : r ≠ .r11) : s₄.gpr r = s₂.gpr r := by rw [h₄.other r h₁ h₂, g₃ r h₃ h₅ h₆ h₇]
  have hlen : (Spec.Aes.bytesAt s₃.mem (P + BitVec.ofNat 64 (16 * kOf L)) (L - 16 * kOf L)).length =
      L - 16 * kOf L := Proof.Cmac.bytesAt_length _ _ _
  have f₄ : Frame [⟨W + BitVec.ofNat 64 32, 32⟩] s₃.mem s₄.mem := by
    rw [h₄.mem]; exact writeBytes_frame _ _ _ (by
      rw [hlen]; simpa using Offset.contains_base (W + BitVec.ofNat 64 32) (d := 0) (n := L - 16 * kOf L) (k := 32)
        (by omega) (by decide))
  have f₃ : Frame [⟨W + BitVec.ofNat 64 144, 8⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have a₄ : s₄.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (16 * kOf L) := by
    rw [f₄.readW (w := 64) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (d := 144) (n := 8) (e := 32) (k := 32) (by omega) (by omega) (by omega))
        (by decide), m₃, Mem.readW_writeW_self64]
  obtain ⟨s₅, run₅, r13₅, rcx₅, g₅, m₅, rd₅, wr₅⟩ := t2a_ok (P := P) (W := W) (L := L) (a := 16 * kOf L) (by omega)
    (by rw [h₄.other _ (by decide) (by decide), r13₃])
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r14])
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r15])
    (by rw [h₄.other _ (by decide) (by decide), r11₃])
  obtain ⟨s₆, run₆, m₆, g₆, rd₆, wr₆⟩ := t2b_ok h hT.1 hT.2 rcx₅
    (by rw [g₅ _ (by decide) (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hr₂.r12]) (by rw [rd₅, h₄.rd, rd₃']) (by rw [wr₅, h₄.wr, wr₃'])
  refine WP.of_runBlock ⟨s₆, by
    rw [show ([.alu .sub .r13 (.reg .r11), .mov .rcx (.reg .r14),
        .alu .sub .rcx (.reg .r11), .alu .add .rcx (.reg .r15),
        .mov .rax (.mem (at_ .rcx (tailOff - 16))), .alu .xor .rax (.mem (at_ .r12 0)),
        .store (at_ .rcx (tailOff - 16)) .rax, .mov .rax (.mem (at_ .rcx (tailOff - 8))),
        .alu .xor .rax (.mem (at_ .r12 8)), .store (at_ .rcx (tailOff - 8)) .rax] : List Instr) =
        [.alu .sub .r13 (.reg .r11), .mov .rcx (.reg .r14),
        .alu .sub .rcx (.reg .r11), .alu .add .rcx (.reg .r15)] ++
        [.mov .rax (.mem (at_ .rcx (tailOff - 16))), .alu .xor .rax (.mem (at_ .r12 0)),
        .store (at_ .rcx (tailOff - 16)) .rax, .mov .rax (.mem (at_ .rcx (tailOff - 8))),
        .alu .xor .rax (.mem (at_ .r12 8)), .store (at_ .rcx (tailOff - 8)) .rax] from rfl,
      runBlock_append, run₅, Option.bind_some, run₆], ?_⟩
  have keep (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .r10) (h₃ : r ≠ .r13) (h₅ : r ≠ .rcx) (h₆ : r ≠ .rdx)
      (h₇ : r ≠ .r11) : s₆.gpr r = s₂.gpr r := by rw [g₆ r h₁, g₅ r h₃ h₅, g₄ r h₁ h₂ h₃ h₅ h₆ h₇]
  have f₆ : Frame [⟨W + BitVec.ofNat 64 32, 32⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact (xor2Mem_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨W + BitVec.ofNat 64 32, 32⟩, List.mem_singleton_self _,
        Offset.sub_base (W + BitVec.ofNat 64 32) (d := L - 16 * kOf L - 16) (n := 16) (k := 32) (by omega)⟩
  refine ⟨⟨by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rbx],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rbp],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r12],
      by rw [g₆ _ (by decide), r13₅],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r14],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r15],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rsp],
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

/-! ## The calls -/

/-- The arguments of the update over the `k` blocks of `P`. -/
theorem m1_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) (hL16 : 16 ≤ L)
    (ha : s.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = BitVec.ofNat 64 (16 * kOf L)) :
    ∃ s', runBlock isa (zero16 .r15 out ++
        ([.mov .r8 (.mem (at_ .r15 dbOff)), .shift .shr .r8 4, .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp),
         .mov .rdx (.reg .r15), .alu .add .rdx (imm out), .mov .rcx (.reg .r13), .mov .r9 (.reg .r15),
         .alu .add .r9 (imm csOff)] : List Instr)) s = some s' ∧ Regs s₀ C D P W R L s' ∧
      UArgs s' C (W + BitVec.ofNat 64 out) P (W + BitVec.ofNat 64 256) R (kOf L) ∧
      s'.mem = zero2 s.mem (W + BitVec.ofNat 64 out) := by
  have hT := kOf_tail hL16
  have hlt := h.lt
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := h.zero16_ok hr.r15 hr.wr (d := out) (by omega)
  have hr₁ := hr.keep (fun r hr' => g₁ r (by rintro rfl; simp [calleeSaved] at hr')) rd₁ wr₁
  have ha₁ : s₁.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = BitVec.ofNat 64 (16 * kOf L) := by
    rw [m₁, zero2, (frame_store2 _ _ _).readW (w := 64) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (d := dbOff) (n := 8) (e := out) (k := 16) (by simp only [dbOff]; omega)
        (by simp only [dbOff]; omega) (by omega)) (by decide), ha]
  have r := h.inRW hr₁.rd hr₁.wr (d := dbOff) (n := 8) (by decide)
  obtain ⟨s₂, run₂, hr₂, rdi, rsi, rdx, rcx, r8, r9, m₂⟩ : ∃ s₂, runBlock isa
      [.mov .r8 (.mem (at_ .r15 dbOff)), .shift .shr .r8 4, .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp),
       .mov .rdx (.reg .r15), .alu .add .rdx (imm out), .mov .rcx (.reg .r13), .mov .r9 (.reg .r15),
       .alu .add .r9 (imm csOff)] s₁ = some s₂ ∧ Regs s₀ C D P W R L s₂ ∧ s₂.gpr .rdi = C ∧
      s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = W + BitVec.ofNat 64 out ∧ s₂.gpr .rcx = P ∧
      s₂.gpr .r8 = BitVec.ofNat 64 (kOf L) ∧ s₂.gpr .r9 = W + BitVec.ofNat 64 256 ∧ s₂.mem = s₁.mem := by
    refine ⟨_, by
      simp (config := {decide := true}) only [imm, csOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
        readSrc, execAlu, execShift, State.load64, State.ea, offset_nat, Option.bind_some, Option.map_some,
        gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, hr₁.r15, r]
      rfl, ?_⟩
    refine ⟨hr₁.keep (fun r hr' => ?_) rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_setFlags]
    all_goals simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
      mem_arithFlags, mem_setFlags, ite_true, ite_false, hr₁.rbx, hr₁.rbp, hr₁.r13, ha₁,
      sx_ofNat (show out < 2 ^ 31 by omega), sx_ofNat (show 256 < 2 ^ 31 by decide),
      shr4 (show 16 * kOf L < 2 ^ 64 by omega), Nat.mul_div_cancel_left _ (show 0 < 16 by decide)]
  refine ⟨s₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], hr₂,
    h.uargs hr₂.rd hr₂.wr hr₂.rsp (by omega) (h.srcData₀ (by omega) (by omega)) (by omega) rdi rsi rdx rcx r8 r9,
    by rw [m₂, m₁]⟩

theorem jOf_le (L : Nat) : jOf L ≤ 1 := by unfold jOf; split <;> omega

theorem m2_ok {s : State} (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (hL : L < 2 ^ 64) :
    ∃ s₁, runBlock isa [.mov32 .r8 (.imm 0), .alu .cmp .r14 (imm 17)] s = some s₁ ∧ s₁.gpr .r8 = 0 ∧
      s₁.cf = some (decide (L < 17)) ∧ (∀ r, r ≠ .r8 → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
      State.setReg32, Option.bind_some, Option.map_some]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · rw [cf_arithFlags]
    simp only [gpr_setReg, ite_false, reduceCtorEq, h14, sx_ofNat (show 17 < 2 ^ 31 by decide),
      toNat_ofNat hL, toNat_ofNat (show 17 < 2 ^ 64 by decide)]
  · intro r hr; simp [gpr_setReg, hr]
  all_goals rfl

/-- `j` in `r8`. -/
theorem jIte_wp {s : State} (h8 : s.gpr .r8 = 0) (hcf : s.cf = some (decide (L < 17))) :
    WP isa (.ite .b (.block []) (.block [.mov32 .r8 (imm 1)])) s fun s' =>
      s'.gpr .r8 = BitVec.ofNat 64 (jOf L) ∧ (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.ite (decide (L < 17)) hcf (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h17 : L < 17 := of_decide_eq_true hb
    exact ⟨by rw [h8]; simp [jOf, h17], fun _ _ => rfl, rfl, rfl, rfl⟩
  · have h17 : ¬ L < 17 := of_decide_eq_false hb
    refine WP.of_runBlock ⟨_, by
      simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [gpr_setReg_self]; simp [jOf, h17]
    · intro r hr; rw [gpr_setReg_of_ne _ _ hr]
    all_goals rfl

/-- The arguments of the update over the first `j` blocks of the tail. -/
theorem m3_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) (h8 : s.gpr .r8 = BitVec.ofNat 64 (jOf L)) :
    ∃ s', runBlock isa [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm out), .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff),
        .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff), .store (at_ .r15 (dbOff + 8)) .r8] s = some s' ∧
      Regs s₀ C D P W R L s' ∧
      UArgs s' C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) R (jOf L) ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 (dbOff + 8)) (BitVec.ofNat 64 (jOf L)) := by
  have hj := jOf_le L
  have w := h.inW hr.wr (d := dbOff + 8) (n := 8) (by decide)
  obtain ⟨s', run, hr', rdi, rsi, rdx, rcx, r8, r9, m⟩ : ∃ s', runBlock isa [.mov .rdi (.reg .rbx),
      .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (imm out), .mov .rcx (.reg .r15),
      .alu .add .rcx (imm tailOff), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff),
      .store (at_ .r15 (dbOff + 8)) .r8] s = some s' ∧ Regs s₀ C D P W R L s' ∧ s'.gpr .rdi = C ∧
      s'.gpr .rsi = BitVec.ofNat 64 R ∧ s'.gpr .rdx = W + BitVec.ofNat 64 out ∧
      s'.gpr .rcx = W + BitVec.ofNat 64 32 ∧ s'.gpr .r8 = BitVec.ofNat 64 (jOf L) ∧
      s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 (dbOff + 8)) (BitVec.ofNat 64 (jOf L)) := by
    refine ⟨_, by
      simp (config := {decide := true}) only [imm, tailOff, csOff, runBlock_cons, runStep_some, runBlock_nil, at_,
        exec, readSrc, execAlu, State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg,
        gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true,
        ite_false, hr.r15, w]
      rfl, ?_⟩
    refine ⟨hr.keep (fun r hr' => ?_) rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags,
      ite_true, ite_false, hr.rbx, hr.rbp, h8, sx_ofNat (show out < 2 ^ 31 by omega),
      sx_ofNat (show 32 < 2 ^ 31 by decide), sx_ofNat (show 256 < 2 ^ 31 by decide)]
  exact ⟨s', run, hr', h.uargs hr'.rd hr'.wr hr'.rsp (by omega)
    (h.srcWork (o := out) (t := 32) (n := 16 * jOf L) (by omega) (by omega) (by omega)) (by omega)
    rdi rsi rdx rcx r8 r9, m⟩

/-- The arguments of the finalization of the rest of the tail. -/
theorem m4_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) (hL16 : 16 ≤ L)
    (ha : s.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = BitVec.ofNat 64 (16 * kOf L))
    (hj : s.mem.readW (W + BitVec.ofNat 64 (dbOff + 8)) 64 = BitVec.ofNat 64 (jOf L)) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .r15 (dbOff + 8))), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .mov .r8 (.reg .r14), .alu .sub .r8 (.mem (at_ .r15 dbOff)), .alu .sub .r8 (.reg .rax),
        .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .alu .add .rcx (.reg .rax),
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm out), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)] s = some s' ∧
      Regs s₀ C D P W R L s' ∧
      FArgs s' C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (W + BitVec.ofNat 64 256)
        (L - 16 * kOf L - 16 * jOf L) R ∧ s'.mem = s.mem := by
  have hT := kOf_tail hL16
  have hJ := jOf_rest hL16
  have hj1 := jOf_le L
  have hlt := h.lt
  have r₁ := h.inRW hr.rd hr.wr (d := dbOff + 8) (n := 8) (by decide)
  have r₂ := h.inRW hr.rd hr.wr (d := dbOff) (n := 8) (by decide)
  obtain ⟨s', run, hr', rdi, rsi, rdx, rcx, r8, r9, m⟩ : ∃ s', runBlock isa
      [.mov .rax (.mem (at_ .r15 (dbOff + 8))), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .mov .r8 (.reg .r14), .alu .sub .r8 (.mem (at_ .r15 dbOff)), .alu .sub .r8 (.reg .rax),
        .mov .rcx (.reg .r15), .alu .add .rcx (imm tailOff), .alu .add .rcx (.reg .rax),
        .mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
        .alu .add .rdx (imm out), .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)] s = some s' ∧
      Regs s₀ C D P W R L s' ∧ s'.gpr .rdi = C ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧
      s'.gpr .rdx = W + BitVec.ofNat 64 out ∧ s'.gpr .rcx = W + BitVec.ofNat 64 (32 + 16 * jOf L) ∧
      s'.gpr .r8 = BitVec.ofNat 64 (L - 16 * kOf L - 16 * jOf L) ∧ s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧
      s'.mem = s.mem := by
    refine ⟨_, by
      simp (config := {decide := true}) only [imm, tailOff, csOff, runBlock_cons, runStep_some, runBlock_nil, at_,
        exec, readSrc, execAlu, State.load64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg,
        gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true,
        ite_false, hr.r15, r₁, r₂]
      rfl, ?_⟩
    refine ⟨hr.keep (fun r hr' => ?_) rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
      ite_true, ite_false, hr.rbx, hr.rbp, hr.r14, ha, hj, dbl4 (jOf L) (by omega),
      sx_ofNat (show out < 2 ^ 31 by omega), sx_ofNat (show 32 < 2 ^ 31 by decide),
      sx_ofNat (show 256 < 2 ^ 31 by decide), Offset.add_add, Offset.ofNat_sub_ofNat (show 16 * kOf L ≤ L by omega),
      Offset.ofNat_sub_ofNat (show 16 * jOf L ≤ L - 16 * kOf L by omega)]
  exact ⟨s', run, hr', h.fargs hr'.rd hr'.wr hr'.rsp (by omega)
    (h.srcWork (o := out) (t := 32 + 16 * jOf L) (n := L - 16 * kOf L - 16 * jOf L) (by omega) (by omega)
      (by omega)) (by omega) rdi rsi rdx rcx r8 r9, m⟩

/-! ## The whole long case -/

/-- The regions `longMac` writes. -/
abbrev macRegions (W : Addr) (out : Nat) (sp : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 144, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below sp 16]

/-- What `longMac` leaves: CMAC's last step on the tail's last bytes, after the
`k` blocks of `P` and the first `j` blocks of the tail, all as they were. -/
structure LMac (s₀ : State) (C D P W : Addr) (R L out : Nat) (s s' : State) : Prop where
  regs : Regs s₀ C D P W R L s'
  frame : Frame (macRegions W out (s₀.gpr .rsp)) s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 out) 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem C (16 * (R + 1)))
      (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 240) 16)
          (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 256) 16)
          (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 (32 + 16 * jOf L)) (L - 16 * kOf L - 16 * jOf L)))
        (Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem C (16 * (R + 1))))
          (Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem C (16 * (R + 1)))) (Spec.Cmac.zeros 16)
            (Spec.Cmac.blocks 16 (Spec.Aes.bytesAt s.mem P (16 * kOf L))))
          (Spec.Cmac.blocks 16 (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 32) (16 * jOf L)))))

theorem longMac_wp (v : Ctr32Impl) (h : Env s₀ C D P W R L) {s₁ : State} (hr₁ : Regs s₀ C D P W R L s₁)
    (hL16 : 16 ≤ L) {out : Nat} (hout : out = 0 ∨ out = 112)
    (ha : s₁.mem.readW (W + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 (16 * kOf L)) :
    WP isa (longMac v.callee v.suffix out) s₁ (LMac s₀ C D P W R L out s₁) := by
  have hwW := h.wW
  have hlt := h.lt
  have hT := kOf_tail hL16
  have hJ := jOf_rest hL16
  have hj1 := jOf_le L
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  obtain ⟨s₂, run₂, hr₂, u₂, m₂⟩ := m1_ok h hr₁ hout hL16 ha
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.seq (WP.mono (upd_call v _ u₂) fun s₃ h₃ => ?_)
  have hr₃ := hr₂.keep h₃.saved h₃.rd h₃.wr
  obtain ⟨s₄', run₄', r8₄', cf₄', g₄', m₄', rd₄', wr₄'⟩ := m2_ok hr₃.r14 hlt
  refine WP.seq (WP.of_runBlock ⟨s₄', run₄', ?_⟩)
  refine WP.seq (WP.mono (jIte_wp r8₄' cf₄') fun s₄ ⟨r8₄, g₄'', m₄'', rd₄'', wr₄''⟩ => ?_)
  have g₄ (r : Reg) (hr' : r ≠ .r8) : s₄.gpr r = s₃.gpr r := by rw [g₄'' r hr', g₄' r hr']
  have m₄ : s₄.mem = s₃.mem := by rw [m₄'', m₄']
  have rd₄ : s₄.rd = s₃.rd := by rw [rd₄'', rd₄']
  have wr₄ : s₄.wr = s₃.wr := by rw [wr₄'', wr₄']
  have hr₄ := hr₃.keep (fun r hr' => g₄ r (by rintro rfl; simp [calleeSaved] at hr')) rd₄ wr₄
  obtain ⟨s₅, run₅, hr₅, u₅, m₅⟩ := m3_ok h hr₄ hout r8₄
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  refine WP.seq (WP.mono (upd_call v _ u₅) fun s₆ h₆ => ?_)
  have hr₆ := hr₅.keep h₆.saved h₆.rd h₆.wr
  -- The frames of the calls.
  have dO (d n : Nat) (hd : d + n ≤ 256) (hs : d + n ≤ out ∨ out + 16 ≤ d) (r : Region)
      (hr' : r ∈ [(⟨W + BitVec.ofNat 64 out, 16⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact Offset.disjoint W hs (by omega) (by omega)
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact (h.stk_w.sub_right (h.sW (by omega))).symm
  have f₃ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₂.mem s₃.mem := by rw [← hr₂.rsp]; exact h₃.frame
  have f₆ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₅.mem s₆.mem := by rw [← hr₅.rsp]; exact h₆.frame
  have ha₆ : s₆.mem.readW (W + BitVec.ofNat 64 dbOff) 64 = BitVec.ofNat 64 (16 * kOf L) := by
    have c := Region.contains_self (W + BitVec.ofNat 64 dbOff) 8
    rw [f₆.readW c (dO 144 8 (by decide) (by omega)) (by decide), m₅,
      Mem.readW_writeW_sep (Offset.sep W (d := dbOff) (n := 8) (e := dbOff + 8) (k := 8) (by decide) (by decide)
        (by decide)) (by decide), m₄, f₃.readW c (dO 144 8 (by decide) (by omega)) (by decide), m₂, zero2,
      (frame_store2 _ _ _).readW (w := 64) c (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (d := dbOff) (n := 8) (e := out) (k := 16) (by simp only [dbOff]; omega)
          (by simp only [dbOff]; omega) (by omega)) (by decide)]
    exact ha
  have hj₆ : s₆.mem.readW (W + BitVec.ofNat 64 (dbOff + 8)) 64 = BitVec.ofNat 64 (jOf L) := by
    rw [f₆.readW (Region.contains_self _ 8) (dO 152 8 (by decide) (by omega)) (by decide), m₅,
      Mem.readW_writeW_self64]
  obtain ⟨s₇, run₇, hr₇, fa₇, m₇⟩ := m4_ok h hr₆ hout hL16 ha₆ hj₆
  refine WP.seq (WP.of_runBlock ⟨s₇, run₇, ?_⟩)
  refine WP.mono (finr_call v _ fa₇) fun s₈ h₈ => ?_
  have f₈ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
      s₇.mem s₈.mem := by rw [← hr₇.rsp]; exact h₈.frame
  -- Everything after the tail, as one frame.
  have f₂ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩] s₁.mem s₂.mem := by rw [m₂]; exact frame_store2 _ _ _
  have f₅ : Frame [⟨W + BitVec.ofNat 64 144, 16⟩] s₄.mem s₅.mem := by
    have c : (⟨W + BitVec.ofNat 64 144, 16⟩ : Region).Contains (W + BitVec.ofNat 64 (dbOff + 8)) 8 := by
      rw [show W + BitVec.ofNat 64 (dbOff + 8) = W + BitVec.ofNat 64 144 + BitVec.ofNat 64 8 from
        (Offset.add_add _ _ _).symm]
      exact Offset.contains_base _ (d := 8) (n := 8) (k := 16) (by decide) (by decide)
    rw [m₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c
  let rs : List Region := [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 144, 16⟩,
    ⟨W + BitVec.ofNat 64 256, 2176⟩, below (s₀.gpr .rsp) 16]
  have sub (xs : List Region) (hx : ∀ r ∈ xs, r ∈ rs) : ∀ r ∈ xs, ∃ r' ∈ rs, Region.Sub r r' :=
    fun r hr => ⟨r, hx r hr, fun _ h => h⟩
  have f₄ : Frame rs s₃.mem s₄.mem := by rw [m₄]; exact Frame.refl _ _
  have f₇ : Frame rs s₆.mem s₇.mem := by rw [m₇]; exact Frame.refl _ _
  have g₂₅ : Frame rs s₁.mem s₅.mem :=
    (((f₂.sub (sub _ (by simp [rs]))).trans (f₃.sub (sub _ (by simp [rs])))).trans f₄).trans
      (f₅.sub (sub _ (by simp [rs])))
  have g₂₇ : Frame rs s₁.mem s₇.mem := (g₂₅.trans (f₆.sub (sub _ (by simp [rs])))).trans f₇
  have g₂₈ : Frame rs s₁.mem s₈.mem := g₂₇.trans (f₈.sub (sub _ (by simp [rs])))
  refine ⟨hr₇.keep h₈.saved h₈.rd h₈.wr, g₂₈, ?_⟩
  have dC {m : Mem} (hm : Frame rs s₁.mem m) {d n : Nat} (hd : d + n ≤ 512) :
      Spec.Aes.bytesAt m (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₁.mem (C + BitVec.ofNat 64 d) n :=
    bytesAt_frame hm (fun r hr => by
      have hc := h.c_w.sub_left (h.sC hd)
      simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hc.sub_right (h.sW (by omega))
      · exact hc.sub_right (h.sW (by decide))
      · exact hc.sub_right (h.sW (by decide))
      · exact (h.stk_c.sub_right (h.sC hd)).symm) (by omega)
  have dP {m : Mem} (hm : Frame rs s₁.mem m) {d n : Nat} (hd : d + n ≤ L) :
      Spec.Aes.bytesAt m (P + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₁.mem (P + BitVec.ofNat 64 d) n :=
    bytesAt_frame hm (fun r hr => by
      have hc := h.p_w.sub_left (h.sP hd)
      simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hc.sub_right (h.sW (by omega))
      · exact hc.sub_right (h.sW (by decide))
      · exact hc.sub_right (h.sW (by decide))
      · exact (h.stk_p.sub_right (h.sP hd)).symm) (by omega)
  have dT {m : Mem} (hm : Frame rs s₁.mem m) {d n : Nat} (hd : 32 ≤ d) (hd' : d + n ≤ 64) :
      Spec.Aes.bytesAt m (W + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 d) n :=
    bytesAt_frame hm (fun r hr => by
      simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact Offset.disjoint W (by omega) (by omega) (by omega)
      · exact (h.stk_w.sub_right (h.sW (by omega))).symm) (by omega)
  have F₂ : Frame rs s₁.mem s₂.mem := f₂.sub (sub _ (by simp [rs]))
  have o₅ : Spec.Aes.bytesAt s₅.mem (W + BitVec.ofNat 64 out) 16 = Spec.Aes.bytesAt s₄.mem (W + BitVec.ofNat 64 out) 16 :=
    bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
      (by decide)
  have hz : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂]; exact zero2_bytes _ _
  have sch₂ := dC F₂ (d := 0) (n := 16 * (R + 1)) (by omega)
  have sch₅ := dC g₂₅ (d := 0) (n := 16 * (R + 1)) (by omega)
  have sch₇ := dC g₂₇ (d := 0) (n := 16 * (R + 1)) (by omega)
  rw [k0] at sch₂ sch₅ sch₇
  have k1 := dC g₂₇ (d := 240) (n := 16) (by decide)
  have k2 := dC g₂₇ (d := 256) (n := 16) (by decide)
  have pk := dP F₂ (d := 0) (n := 16 * kOf L) (by omega)
  rw [k0] at pk
  have t₅ := dT g₂₅ (d := 32) (n := 16 * jOf L) (by decide) (by omega)
  have t₇ := dT g₂₇ (d := 32 + 16 * jOf L) (n := L - 16 * kOf L - 16 * jOf L) (by omega) (by omega)
  rw [h₈.out, mn, sch₇, k1, k2, t₇, m₇, h₆.out, Proof.Cmac.Stream.blocksAt_eq, sch₅, t₅, o₅, m₄, h₃.out,
    Proof.Cmac.Stream.blocksAt_eq, sch₂, pk, hz]

/-- S2V's end for a string of a block or more, as `longMac` computes it. -/
theorem long_spec (ciph : Spec.Cmac.Cipher) (k1 k2 d p : List Byte) (hd : d.length = 16) (hL16 : 16 ≤ p.length) :
    ciph (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 k1 k2
          ((Spec.Siv.xorend (p.drop (16 * kOf p.length)) d).drop (16 * jOf p.length)))
        (Spec.Cmac.chain ciph (Spec.Cmac.chain ciph (Spec.Cmac.zeros 16)
            (Spec.Cmac.blocks 16 (p.take (16 * kOf p.length))))
          (Spec.Cmac.blocks 16 ((Spec.Siv.xorend (p.drop (16 * kOf p.length)) d).take (16 * jOf p.length))))) =
      Spec.Siv.s2vFinish (Spec.Siv.cmacWith ciph k1 k2) d p := by
  have hT := kOf_tail hL16
  have hJ := jOf_rest hL16
  have hlT : (Spec.Siv.xorend (p.drop (16 * kOf p.length)) d).length = p.length - 16 * kOf p.length := by
    rw [Siv.length_xorend (by rw [List.length_drop, hd]; omega), List.length_drop]
  rw [Siv.s2vFinish_long _ hd (a := 16 * kOf p.length) (by omega)]
  generalize Spec.Siv.xorend (List.drop (16 * kOf p.length) p) d = tl at hlT ⊢
  conv => rhs; rw [← List.take_append_drop (16 * jOf p.length) tl]
  rw [← List.append_assoc, Siv.cmacWith_split₂ _ _ _ (by rw [List.length_take]; omega)
      (by rw [List.length_take, hlT]; omega) (by rw [List.length_drop, hlT]; omega)
      (Or.inr (by rw [List.length_drop, hlT]; omega)), Proof.Cmac.xor_comm]

theorem finishLong_wp (v : Ctr32Impl) (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s)
    (hL16 : 16 ≤ L) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (.seq longTail (longMac v.callee v.suffix out)) s (FinPost s₀ C D P W R L out s) := by
  have hwW := h.wW
  have hlt := h.lt
  have hT := kOf_tail hL16
  have hJ := jOf_rest hL16
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  refine WP.seq (WP.mono (longTail_wp h hr hL16) fun s₁ h₁ => ?_)
  refine WP.mono (longMac_wp v h h₁.regs hL16 hout h₁.a) fun s₂ h₂ => ?_
  have f₁ : Frame (finRegions W out (s₀.gpr .rsp)) s.mem s₁.mem := h₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 144, 16⟩, by simp, Region.sub_prefix (by decide)⟩
  have f₂ : Frame (finRegions W out (s₀.gpr .rsp)) s₁.mem s₂.mem := h₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨h₂.regs, f₁.trans f₂, ?_⟩
  have dC {d n : Nat} (hd : d + n ≤ 512) :
      Spec.Aes.bytesAt s₁.mem (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 d) n :=
    bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.c_w.sub_left (h.sC hd)).sub_right (h.sW (by decide))
      · exact (h.c_w.sub_left (h.sC hd)).sub_right (h.sW (by decide))) (by omega)
  have sch := dC (d := 0) (n := 16 * (R + 1)) (by omega)
  have k1 := dC (d := 240) (n := 16) (by decide)
  have k2 := dC (d := 256) (n := 16) (by decide)
  rw [k0] at sch
  have pk : Spec.Aes.bytesAt s₁.mem P (16 * kOf L) = Spec.Aes.bytesAt s.mem P (16 * kOf L) :=
    bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.p_w.sub_left (Region.sub_prefix (by omega))).sub_right (h.sW (by decide))
      · exact (h.p_w.sub_left (Region.sub_prefix (by omega))).sub_right (h.sW (by decide))) (by omega)
  -- The tail, as the calls read it.
  have hTsplit : L - 16 * kOf L = 16 * jOf L + (L - 16 * kOf L - 16 * jOf L) := by omega
  have tk := take_bytesAt s₁.mem (W + BitVec.ofNat 64 32) (a := 16 * jOf L) (b := L - 16 * kOf L - 16 * jOf L)
  have dr := drop_bytesAt s₁.mem (W + BitVec.ofNat 64 32) (a := 16 * jOf L) (b := L - 16 * kOf L - 16 * jOf L)
  rw [← hTsplit, h₁.tail] at tk dr
  rw [Offset.add_add] at dr
  have hLsplit : L = 16 * kOf L + (L - 16 * kOf L) := by omega
  have pt := take_bytesAt s.mem P (a := 16 * kOf L) (b := L - 16 * kOf L)
  have pd := drop_bytesAt s.mem P (a := 16 * kOf L) (b := L - 16 * kOf L)
  rw [← hLsplit] at pt pd
  have hlP : (Spec.Aes.bytesAt s.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
  have hs := long_spec (Spec.Siv.schedCiph s.mem C R) (Spec.Aes.bytesAt s.mem (C + 240) 16)
    (Spec.Aes.bytesAt s.mem (C + 256) 16) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L)
    (Proof.Cmac.bytesAt_length _ _ _) (by rw [hlP]; exact hL16)
  rw [hlP, pt, pd] at hs
  rw [h₂.out, sch, k1, k2, ← dr, ← tk, pk, Spec.Siv.ctxMac, ← hs]
  rfl

end VG.Proof.AesSiv.X86_64
