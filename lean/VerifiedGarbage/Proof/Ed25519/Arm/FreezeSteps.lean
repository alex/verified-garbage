import VerifiedGarbage.Impl.Ed25519.Arm.Freeze
import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory

/-! Canonical reduction of the two temporary field elements. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem low15_val (x : BitVec 32) : ((x <<< 17) >>> 17).toNat = x.toNat % 32768 := by
  rw [toNat_shr, toNat_shl, show (2 : Nat) ^ 32 = 32768 * 2 ^ 17 from rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem sel0r (a c : BitVec 32) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 32 0)) = a := by simp

theorem sel1r (a c : BitVec 32) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 32 1)) = c := by
  have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
  rw [this, BitVec.and_allOnes, BitVec.xor_comm c, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

variable {b : BitVec 32}

/-- The start of `freeze`: bit 255 of `[FR]` cleared, 19 times it in `r5`. -/
theorem freezeA_ok {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) FR) :
    WP isa (.block freezeA) s fun s' =>
      s'.gpr .r6 = mask16 ∧ (s'.gpr .r5).toNat = 19 * (limb s.mem (State.addr b) FR 15 / 32768) ∧
      (∀ k < 16, limb s'.mem (State.addr b) FR k = mask15 (limb s.mem (State.addr b) FR) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 FR, 64⟩] s.mem s'.mem ∧
      Rest [.r2, .r3, .r5, .r6] s s' := by
  have hX : FR = 1472 := rfl
  simp only [freezeA, low15, List.cons_append, List.nil_append]
  refine wp_movw fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r6]) (by decide)) (by decide)
  refine ldr0_ok hc1 (d := FR + 60) (by decide) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => wp_mov (op2_lsl (by decide)) fun s4 u4 =>
    wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  have hr5 : Rest [.r3, .r5, .r6] s s5 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  refine str0_ok hc5 (d := FR + 60) (by decide) fun s6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun s7 u7 => wp_mul fun s8 u8 => WP.block_nil ?_
  have hl15 := hl 15 (by decide)
  have e2 : (s2.gpr .r3).toNat = limb s.mem (State.addr b) FR 15 := by rw [u2.gpr, u1.mem]; rfl
  have e5 : (s5.gpr .r3).toNat = limb s.mem (State.addr b) FR 15 % 32768 := by
    rw [u5.gpr, u4.gpr, low15_val, u3.other .r3 (by decide), e2]
  have e3 : (s3.gpr .r5).toNat = limb s.mem (State.addr b) FR 15 / 32768 := by
    rw [u3.gpr, toNat_shr, e2]
  have hm6 : s6.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (FR + 60)) (s5.gpr .r3) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr, u5.other .r6 (by decide),
      u4.other .r6 (by decide), u3.other .r6 (by decide), u2.other .r6 (by decide), u1.gpr]
  · rw [u8.gpr, u7.other _ (by decide), u7.gpr, u6.gpr, u5.other _ (by decide), u4.other _ (by decide),
      toNat_mul_lt (by rw [e3]; show _ * 19 < _; omega), e3]
    show _ * 19 = _
    omega
  · rw [limb, u8.mem, u7.mem, hm6]
    rcases Nat.lt_or_ge k 15 with h | h
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      simp only [mask15, show k ≠ 15 by omega, ite_false]; rfl
    · rw [show FR + 4 * k = FR + 60 by omega, wd_write_self, e5, show k = 15 by omega]; rfl
  · rw [u8.mem, u7.mem, hm6]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := FR + 60) (n := 4) (Nat.le_add_right _ _) (by omega) (by omega))
  · exact (hr5.mono (by decide)).trans ((u6.rest _).trans ((u7.rest (by decide)).trans (u8.rest (by decide))))

/-- `freezeB`: the mask `-(bit 255 of [FY])` in `r9`, and bit 255 of `[FY]` cleared. -/
theorem freezeB_ok {s : State} (hc : Ctx b s) :
    WP isa (.block freezeB) s fun s' =>
      s'.gpr .r9 = 0 - BitVec.ofNat 32 (limb s.mem (State.addr b) FY 15 / 32768) ∧
      (∀ k < 16, limb s'.mem (State.addr b) FY k = mask15 (limb s.mem (State.addr b) FY) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 FY, 64⟩] s.mem s'.mem ∧ Rest [.r1, .r3, .r9] s s' := by
  have hFY : FY = 1536 := rfl
  simp only [freezeB, low15, List.cons_append, List.nil_append]
  refine ldr0_ok hc (d := FY + 60) (by decide) fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => wp_mov (op2_imm (by decide)) fun s3 u3 =>
    wp_dp (op2_reg _ _) fun s4 u4 => wp_mov (op2_lsl (by decide)) fun s5 u5 =>
    wp_mov (op2_lsr (by decide)) fun s6 u6 => ?_
  have hr6 : Rest [.r1, .r3, .r9] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  refine str0_ok (hc.of_rest hr6 (by decide)) (d := FY + 60) (by decide) fun s7 u7 => WP.block_nil ?_
  have e1 : (s1.gpr .r3).toNat = limb s.mem (State.addr b) FY 15 := by rw [u1.gpr]; rfl
  have hm7 : s7.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (FY + 60)) (s6.gpr .r3) := by
    rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, fun k hk => ?_, ?_, hr6.trans (u7.rest _)⟩
  · rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.gpr]
    show s3.gpr .r1 - s3.gpr .r9 = _
    rw [u3.gpr, u3.other _ (by decide), u2.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shr, e1, toNat_imm (by have := wd_lt s.mem (State.addr b) (FY + 4 * 15); unfold limb; omega)]
  · rw [limb, hm7]
    rcases Nat.lt_or_ge k 15 with h | h
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      simp only [mask15, show k ≠ 15 by omega, ite_false]; rfl
    · rw [show FY + 4 * k = FY + 60 by omega, wd_write_self, u6.gpr, u5.gpr, low15_val, u4.other .r3 (by decide),
        u3.other .r3 (by decide), u2.other .r3 (by decide), e1, show k = 15 by omega]; rfl
  · rw [hm7]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := FY + 60) (n := 4) (Nat.le_add_right _ _) (by omega) (by omega))

theorem freezeCopy_ok {s : State} (hc : Ctx b s) (a : Slot) :
    WP isa (.block (freezeCopy a)) s fun t => Rest [.r3] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 FR, 64⟩] s.mem t.mem ∧
      ∀ k < 16, limb t.mem (State.addr b) FR k = limb s.mem (State.addr b) (offset a) k := by
  have ha := slot_range a
  rw [ACC_eq] at ha
  refine WP.mono (fill_ok (src := fun k => [.ldr .r3 .r0 (offset a + 4 * k)])
    (f := limb s.mem (State.addr b) (offset a)) hc (by decide)
    (fun k hk t ht => ldr0_ok (hc.of_rest ht.rest (by decide)) (by omega)
      fun u hu => WP.block_nil ⟨?_, hu.rest (by decide), hu.mem⟩))
    fun t ht => ⟨ht.rest, ht.frame, ht.outs⟩
  rw [hu.gpr]
  exact wd_frame ht.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by change _ ≤ 1472; omega)) (by omega) (by change 1472 + _ ≤ _; omega)

end VG.Proof.Ed25519.Arm
