import VerifiedGarbage.Impl.Rc2.X86_64.Stream
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! # Streaming RC2-CBC on x86-64: the byte-copy loop -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes VG.Impl.Rc2.X86_64.Stream

/-- The copy routine's registers: none is its index `r10` or byte `r11`. -/
structure CopyRegs (src dst cnt : Reg) : Prop where
  src10 : src ≠ .r10
  src11 : src ≠ .r11
  dst10 : dst ≠ .r10
  dst11 : dst ≠ .r11
  cnt10 : cnt ≠ .r10
  cnt11 : cnt ≠ .r11

theorem ea_at10 (s : State) (b : Reg) (d i : Nat) (hi : s.gpr .r10 = BitVec.ofNat 64 i) :
    s.ea (at10 b d) = s.gpr b + BitVec.ofNat 64 d + BitVec.ofNat 64 i := by
  simp only [State.ea, at10, hi, BitVec.mul_one, Int.ofNat_eq_natCast, BitVec.ofInt_natCast]
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 i)]

theorem copyStep_ok (s : State) {src dst cnt : Reg} (hr : CopyRegs src dst cnt) {S D : Addr} {sd dd i n : Nat}
    (hs : s.gpr src + BitVec.ofNat 64 sd = S) (hd : s.gpr dst + BitVec.ofNat 64 dd = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr cnt = BitVec.ofNat 64 n)
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa (copyBody src sd dst dd cnt) s = some s' ∧
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i) (s.mem (S + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ : s.ea (at10 src sd) = S + BitVec.ofNat 64 i := by rw [ea_at10 s src sd i hi, hs]
  have ea₂ : (s.setReg .r11 ((s.mem (S + BitVec.ofNat 64 i)).setWidth 64)).ea (at10 dst dd) =
      D + BitVec.ofNat 64 i := by
    rw [ea_at10 _ dst dd i (by rw [gpr_setReg_of_ne _ _ (by decide)]; exact hi), gpr_setReg_of_ne _ _ hr.dst11, hd]
  have n₁ : (s.setReg .r11 ((s.mem (S + BitVec.ofNat 64 i)).setWidth 64)).gpr cnt = BitVec.ofNat 64 n := by
    rw [gpr_setReg_of_ne _ _ hr.cnt11, hn]
  refine ⟨_, by
    simp (config := {decide := true}) only [copyBody, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, State.load8, State.store8, Option.bind_some, Option.map_some, ea₁, ea₂, r, w, ite_true,
      wr_setReg, rd_setReg, mem_setReg]
    rfl, ?_⟩
  have h10 : (s.setReg .r11 ((s.mem (S + BitVec.ofNat 64 i)).setWidth 64)).gpr .r10 = BitVec.ofNat 64 i := by
    rw [gpr_setReg_of_ne _ _ (by decide), hi]
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_arithFlags, mem_setReg, gpr_setReg_self,
      BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq]
  · simp only [gpr_arithFlags, gpr_setReg_self, h10]; rfl
  · simp only [zf_arithFlags, gpr_setReg_self, h10, gpr_setReg_of_ne _ _ hr.cnt10, gpr_arithFlags, n₁]; rfl
  · intro r' h₁ h₂
    simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂]

theorem beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
    simpa using this
  · intro he; rw [he]; rfl

theorem guard_ok (s : State) {cnt : Reg} (hc : cnt ≠ .r10) {n : Nat} (hn : s.gpr cnt = BitVec.ofNat 64 n)
    (hn' : n < 2 ^ 64) :
    ∃ s', runBlock isa [.mov32 .r10 (.imm 0), .alu .test cnt (.reg cnt)] s = some s' ∧
      s'.gpr .r10 = BitVec.ofNat 64 0 ∧ s'.zf = some (decide (n = 0)) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.setReg32,
      Option.map_some, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [gpr_arithFlags, gpr_setReg_self]; rfl
  · simp only [zf_arithFlags, gpr_setReg_of_ne _ _ hc, hn, BitVec.and_self, beq_zero hn']
  · intro r h; simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ h]

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

/-- The copy routine: `n` bytes from `S = src + sd` to `D = dst + dd`, for
separate ranges. -/
theorem copy_ok (s : State) {src dst cnt : Reg} (hr : CopyRegs src dst cnt) {S D : Addr} {sd dd n : Nat}
    (hs : s.gpr src + BitVec.ofNat 64 sd = S) (hd : s.gpr dst + BitVec.ofNat 64 dd = D)
    (hn : s.gpr cnt = BitVec.ofNat 64 n) (hn' : n < 2 ^ 64)
    (rd : ∀ i < n, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1)
    (wr : ∀ i < n, InRegions s.wr (D + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk S n).Disjoint ⟨D, n⟩) :
    WP isa (copy src sd dst dd cnt) s fun s' => s'.mem = writeBytes s.mem D (Spec.Rc2.bytesAt s.mem S n) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, zf₁, g₁, mem₁, rd₁, wr₁⟩ := guard_ok s hr.cnt10 hn hn'
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (by simpa [eval] using zf₁) (fun h0 => ?_) (fun h0 => ?_)
  · have h0 : n = 0 := of_decide_eq_true h0
    subst h0
    exact WP.block_nil ⟨by rw [mem₁]; simp [Spec.Rc2.bytesAt, writeBytes_nil],
      fun r h₁ _ => g₁ r h₁, rd₁, wr₁⟩
  have hn₀ : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false h0)
  refine WP.loop (M := isa) (body := .block (copyBody src sd dst dd cnt)) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (Spec.Rc2.bytesAt s.mem S i) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn₀, r10₁, by rw [mem₁]; simp [Spec.Rc2.bytesAt, writeBytes_nil],
      fun r h₁ _ => g₁ r h₁, rd₁, wr₁⟩
  rintro k t ⟨i, rfl, hi, r10, mem, g, trd, twr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := copyStep_ok t hr
    (by rw [g _ hr.src10 hr.src11, hs]) (by rw [g _ hr.dst10 hr.dst11, hd]) r10
    (by rw [g _ hr.cnt10 hr.cnt11, hn]) (by rw [trd, twr]; exact rd i hi) (by rw [twr]; exact wr i hi)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Rc2.bytesAt s.mem S i).length = i := bytesAt_length _ _ _
  have hx : writeBytes s.mem D (Spec.Rc2.bytesAt s.mem S i) (S + BitVec.ofNat 64 i) = s.mem (S + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem D _ (R := ⟨D, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sep _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem D (Spec.Rc2.bytesAt s.mem S (i + 1)) := by
    rw [mem', mem, hx, bytesAt_succ, writeBytes_snoc s.mem D (Spec.Rc2.bytesAt s.mem S i)
      (s.mem (S + BitVec.ofNat 64 i)) (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .r10 → r ≠ .r11 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', trd], by rw [wr', twr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat], hmem, gg,
      by rw [rd', trd], by rw [wr', twr]⟩

end VG.Proof.Rc2.X86_64.Stream
