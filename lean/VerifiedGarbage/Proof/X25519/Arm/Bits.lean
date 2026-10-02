import VerifiedGarbage.Proof.X25519.Arm.Setup

/-!
# X25519 on 32-bit ARM: the bits of the scalar

`bits` stores bit `t` of the decoded (clamped) scalar at byte `BITS + t` of
the working space, for `t < 255` (`bits_ok`).
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (bit)

/-- Bit `t` of the scalar's bytes at `SC`, unclamped. -/
def rawBit (m : Mem) (SC : Addr) (t : Nat) : Nat := ((m (SC + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1

theorem rawBit_le (m : Mem) (SC : Addr) (t : Nat) : rawBit m SC t ≤ 1 := by
  simp only [rawBit]; exact Nat.le_of_lt_succ (Nat.and_lt_two_pow _ (by decide : 1 < 2 ^ 1))

theorem getD_bytesAt (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem strb_byte {v : BitVec 32} {x : Nat} (h : v.toNat = x) :
    v.setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat]

section
variable {b : BitVec 32}

/-- While storing the bits of byte `i`, from `s1` (with the byte in `r4`),
after `j` bits. -/
structure JInv (b : BitVec 32) (i : Nat) (x : Nat) (s1 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r5] s1 s
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 (BITS + 8 * i), j⟩] s1.mem s.mem
  bits : ∀ j' < j, s.mem (State.addr b + BitVec.ofNat 64 (BITS + 8 * i + j')) = BitVec.ofNat 8 ((x >>> j') &&& 1)

theorem bitStep_ok {i j : Nat} (hi : i < 32) (hj : j < 8) {x : Nat} {s1 s : State}
    (hc : Ctx b s1) (h4 : (s1.gpr .r4).toNat = x) (h6 : s1.gpr .r6 = b + BitVec.ofNat 32 (8 * i))
    (h : JInv b i x s1 j s) :
    WP isa (.block ((if j = 0 then ([.dp .and .r5 .r4 (.imm 1)] : List Instr)
      else ([.mov .r5 (.shifted .r4 .lsr j), .dp .and .r5 .r5 (.imm 1)] : List Instr)) ++
      ([.strb .r5 .r6 (BITS + j)] : List Instr))) s
      (JInv b i x s1 (j + 1)) := by
  have hB : BITS = 1280 := rfl
  have hfit := hc.fit
  have e4 : (s.gpr .r4).toNat = x := by rw [h.rest.gpr _ (by decide), h4]
  -- The bit, into `r5`.
  have key : ∀ s2 : State, Rest [.r5] s s2 → s2.mem = s.mem → (s2.gpr .r5).toNat = (x >>> j) &&& 1 →
      WP isa (.block [.strb .r5 .r6 (BITS + j)]) s2 (JInv b i x s1 (j + 1)) := by
    intro s2 hr2 hm2 e5
    have e6 : s2.gpr .r6 = b + BitVec.ofNat 32 (8 * i) := by
      rw [hr2.gpr _ (by decide), h.rest.gpr _ (by decide), h6]
    refine wp_strb (a := State.addr b + BitVec.ofNat 64 (BITS + 8 * i + j)) (by omega)
      (by rw [e6, ea2 hfit (by omega)]; congr 2; omega)
      (by rw [hr2.wr, h.rest.wr]; exact hc.inW (by omega)) fun s3 u3 => WP.block_nil ⟨?_, ?_, fun j' hj' => ?_⟩
    · exact h.rest.trans (hr2.trans (u3.rest _))
    · rw [u3.mem, hm2]
      exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
    · rw [u3.mem, VG.WriteBytes.writeW8_apply, hm2]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
      · rw [iteF (Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))]; exact h.bits j' hj'
      · rw [iteT rfl]; exact strb_byte e5
  by_cases h0 : j = 0
  · subst h0
    simp only [ite_true, List.cons_append, List.nil_append]
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => key s2 (u2.rest (by decide)) u2.mem ?_
    rw [u2.gpr]
    show (s.gpr .r4 &&& 1).toNat = _
    rw [BitVec.toNat_and, e4, Nat.shiftRight_zero]; rfl
  · simp only [h0, ite_false, List.cons_append, List.nil_append]
    refine wp_mov (op2_lsr (by omega)) fun s2 u2 => wp_dp (op2_imm (by decide)) fun s3 u3 =>
      key s3 ((u2.rest (by decide)).trans (u3.rest (by decide))) (by rw [u3.mem, u2.mem]) ?_
    rw [u3.gpr]
    show (s2.gpr .r5 &&& 1).toNat = _
    rw [BitVec.toNat_and, u2.gpr, toNat_shr, e4, Nat.shiftRight_eq_div_pow]; rfl

/-- The loop invariant of `bits` from `s0`, before byte `i`. -/
structure BInv (b : BitVec 32) (sc : BitVec 32) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest [.r1, .r4, .r5, .r6, .r7] s0 s
  r1 : s.gpr .r1 = sc + BitVec.ofNat 32 i
  r6 : s.gpr .r6 = b + BitVec.ofNat 32 (8 * i)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (32 - i)
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 BITS, 8 * i⟩] s0.mem s.mem
  bits : ∀ t < 8 * i, s.mem (State.addr b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (rawBit s0.mem (State.addr sc) t)

theorem bitsBody_ok {sc : BitVec 32} {s0 : State} (hsc : sc.toNat + 32 ≤ 2 ^ 32)
    (hin : (⟨State.addr sc, 32⟩ : Region) ∈ s0.rd ++ s0.wr)
    (hd : Region.Disjoint ⟨State.addr sc, 32⟩ ⟨State.addr b, 4096⟩) {i : Nat} (hi : i < 32) {s : State}
    (h : BInv b sc s0 i s) :
    WP isa (.block bitsBody) s fun s' => BInv b sc s0 (i + 1) s' ∧ s'.z = decide (32 - (i + 1) = 0) := by
  have hB : BITS = 1280 := rfl
  have hfit := h.ctx.fit
  unfold bitsBody
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrb (a := State.addr sc + BitVec.ofNat 64 i) (by decide)
    (by rw [h.r1, BitVec.add_zero]; exact addr_add (by omega))
    (by rw [h.rest.rd, h.rest.wr]; exact in_base hin (by omega) (by omega)) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := h.ctx.of_rest (u1.rest (ws := [.r4]) (by decide)) (by decide)
  -- The byte, as in `s0`.
  have hx : (s1.gpr .r4).toNat = (s0.mem (State.addr sc + BitVec.ofNat 64 i)).toNat := by
    rw [u1.gpr, toNat_setWidth8]
    congr 1
    refine h.frame _ fun r hr hcon => ?_
    rw [List.mem_singleton.mp hr] at hcon
    exact hd _ (Offset.contains_base _ (by omega) (by omega))
      ((Offset.sub_base (State.addr b) (d := BITS) (n := 8 * i) (k := 4096) (by omega)) _ hcon)
  refine WP.append (wp_range_flatMap (M := isa) (JInv b i (s0.mem (State.addr sc + BitVec.ofNat 64 i)).toNat s1)
    (fun j s' hj h' => bitStep_ok hi hj hc1 hx (by rw [u1.other _ (by decide), h.r6]) h') 8 (Nat.le_refl _) s1
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s2 h2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => wp_dp (op2_imm (by decide)) fun s4 u4 =>
    wp_subs (op2_imm (by decide)) fun s5 u5 hz => WP.block_nil ?_
  have hr5 : Rest [.r1, .r4, .r5, .r6, .r7] s s5 :=
    (u1.rest (by decide)).trans ((h2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hm5 : s5.mem = s2.mem := by rw [u5.mem, u4.mem, u3.mem]
  have r7' : s5.gpr .r7 = BitVec.ofNat 32 (32 - (i + 1)) := by
    rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), h2.rest.gpr _ (by decide),
      u1.other _ (by decide), h.r7]
    have t1 : (1 : BitVec 32).toNat = 1 := rfl
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sub_le (by rw [toNat_imm (by omega), t1]; omega), toNat_imm (by omega), toNat_imm (by omega), t1]
    omega
  refine ⟨⟨h.ctx.of_rest hr5 (by decide), h.rest.trans hr5, ?_, ?_, r7', ?_, fun t ht => ?_⟩, ?_⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr]
    show s2.gpr .r1 + BitVec.ofNat 32 1 = _
    rw [h2.rest.gpr _ (by decide), u1.other _ (by decide), h.r1, Offset.add_add]
  · rw [u5.other _ (by decide), u4.gpr]
    show s3.gpr .r6 + BitVec.ofNat 32 8 = _
    rw [u3.other _ (by decide), h2.rest.gpr _ (by decide), u1.other _ (by decide), h.r6, Offset.add_add,
      Nat.mul_succ]
  · rw [hm5]
    refine (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).trans ?_
    rw [← u1.mem]
    exact h2.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)⟩
  · rw [hm5]
    rcases Nat.lt_or_ge t (8 * i) with ht' | ht'
    · rw [h2.frame _ fun r hr hcon => by
        rw [List.mem_singleton.mp hr] at hcon
        exact Offset.disjoint (State.addr b) (d := BITS + t) (n := 1) (e := BITS + 8 * i) (k := 8)
          (.inl (by omega)) (by omega) (by omega) _ (Region.contains_self _ _) hcon, u1.mem]
      exact h.bits t ht'
    · have := h2.bits (t - 8 * i) (by omega)
      rw [show BITS + 8 * i + (t - 8 * i) = BITS + t by omega] at this
      rw [this]
      simp only [rawBit, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  · rw [hz, ← u5.gpr, r7', ofNat_beq_zero (by omega)]

theorem bits_ok {sc : BitVec 32} {s : State} (hc : Ctx b s) (h1 : s.gpr .r1 = sc)
    (hsc : sc.toNat + 32 ≤ 2 ^ 32) (hin : (⟨State.addr sc, 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨State.addr sc, 32⟩ ⟨State.addr b, 4096⟩) :
    WP isa bits s fun s' => Ctx b s' ∧ Rest [.r1, .r4, .r5, .r6, .r7] s s' ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 BITS, 256⟩] s.mem s'.mem ∧
      Bits b (VG.Spec.X25519.decodeScalar25519 (bytesAt s.mem (State.addr sc) 32)) s'.mem := by
  have hB : BITS = 1280 := rfl
  have hfit := hc.fit
  unfold bits
  refine WP.seq (wp_mov (op2_reg _ _) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => WP.block_nil ?_)
  have hr2 : Rest [.r6, .r7] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have h0 : BInv b sc s2 0 s2 :=
    ⟨hc.of_rest hr2 (by decide), Rest.refl _ _, by rw [hr2.gpr _ (by decide), h1]; exact (BitVec.add_zero _).symm,
      by rw [u2.other _ (by decide), u1.gpr, hc.r0]; exact (BitVec.add_zero _).symm, by rw [u2.gpr]; rfl,
      Frame.refl _ _, fun t ht => absurd ht (by omega)⟩
  refine WP.seq (WP.mono (Q := BInv b sc s2 32) (WP.loop (M := isa)
    (fun m s' => ∃ i, m = 32 - i ∧ i < 32 ∧ BInv b sc s2 i s') ?_ 32 s2 ⟨0, rfl, by decide, h0⟩)
    fun s3 h3 => ?_)
  · rintro m s' ⟨i, rfl, hi, hb⟩
    refine WP.mono (bitsBody_ok hsc (by rw [hr2.rd, hr2.wr]; exact hin) hd hi hb) fun s'' ⟨hb', hz⟩ => ?_
    by_cases h32 : i + 1 = 32
    · exact .inl ⟨by rw [eval_ne, hz]; simp [h32], by rw [h32] at hb'; exact hb'⟩
    · exact .inr ⟨by rw [eval_ne, hz]; simp; omega, 32 - (i + 1), by omega, i + 1, rfl, by omega, hb'⟩
  -- The clamping.
  have hc3 := h3.ctx
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  have hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := [.r5]) (by decide)) (by decide)
  have st : ∀ (t : State), Ctx b t → ∀ d, d < 4096 → State.addr (t.gpr .r0 + BitVec.ofNat 32 d) =
      State.addr b + BitVec.ofNat 64 d := fun t ht d hd => ht.ea hd
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 BITS) (by decide) (st _ hc4 _ (by omega))
    (hc4.inW (by omega)) fun s5 u5 => ?_
  have hc5 : Ctx b s5 := hc4.of_rest (u5.rest []) (by decide)
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (BITS + 1)) (by decide) (st _ hc5 _ (by omega))
    (hc5.inW (by omega)) fun s6 u6 => ?_
  have hc6 : Ctx b s6 := hc5.of_rest (u6.rest []) (by decide)
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (BITS + 2)) (by decide) (st _ hc6 _ (by omega))
    (hc6.inW (by omega)) fun s7 u7 => ?_
  have hc7 : Ctx b s7 := hc6.of_rest (u7.rest []) (by decide)
  refine wp_mov (op2_imm (by decide)) fun s8 u8 => ?_
  have hc8 : Ctx b s8 := hc7.of_rest (u8.rest (ws := [.r5]) (by decide)) (by decide)
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (BITS + 254)) (by decide) (st _ hc8 _ (by omega))
    (hc8.inW (by omega)) fun s9 u9 => WP.block_nil ?_
  have v0 : (s4.gpr .r5).setWidth 8 = 0 := by rw [u4.gpr]; rfl
  have v1 : (s8.gpr .r5).setWidth 8 = 1 := by rw [u8.gpr]; rfl
  have hm9 : s9.mem = (((s3.mem.writeW (State.addr b + BitVec.ofNat 64 BITS) (0 : BitVec 8)).writeW
      (State.addr b + BitVec.ofNat 64 (BITS + 1)) (0 : BitVec 8)).writeW
      (State.addr b + BitVec.ofNat 64 (BITS + 2)) (0 : BitVec 8)).writeW
      (State.addr b + BitVec.ofNat 64 (BITS + 254)) (1 : BitVec 8) := by
    rw [u9.mem, v1, u8.mem, u7.mem, u6.gpr, u5.gpr, v0, u6.mem, u5.gpr, v0, u5.mem, v0, u4.mem]
  have ne : ∀ a c : Nat, a < 256 → c < 256 → a ≠ c →
      State.addr b + BitVec.ofNat 64 (BITS + a) ≠ State.addr b + BitVec.ofNat 64 (BITS + c) :=
    fun a c ha hc' hac => Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
  have hr9 : Rest [.r1, .r4, .r5, .r6, .r7] s s9 :=
    (hr2.mono (by decide)).trans ((h3.rest).trans ((u4.rest (by decide)).trans ((u5.rest _).trans
      ((u6.rest _).trans ((u7.rest _).trans ((u8.rest (by decide)).trans (u9.rest _)))))))
  refine ⟨hc3.of_rest ((u4.rest (ws := [.r5]) (by decide)).trans ((u5.rest _).trans ((u6.rest _).trans
    ((u7.rest _).trans ((u8.rest (by decide)).trans (u9.rest _)))))) (by decide), hr9, ?_, fun t ht => ?_⟩
  · rw [hm9, ← hm2]
    have m := List.mem_singleton_self (⟨State.addr b + BitVec.ofNat 64 BITS, 256⟩ : Region)
    refine ((((h3.frame.sub fun r hr => ⟨_, m, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW m _ ?_).writeW m _ ?_).writeW m _ ?_).writeW
      m _ ?_ <;> exact Offset.contains _ (n := 1) (by omega) (by omega) (by omega)
  · have hbit := VG.Proof.X25519.scalar_bit (length_bytesAt s.mem (State.addr sc) 32) ht
    rw [getD_bytesAt _ _ (by omega)] at hbit
    rw [hbit, hm9]
    simp only [VG.WriteBytes.writeW8_apply]
    by_cases t254 : t = 254
    · subst t254; rw [iteT rfl]; rfl
    rw [iteF (ne _ _ (by omega) (by omega) t254)]
    by_cases t2 : t = 2
    · subst t2; rw [iteT rfl]; rfl
    rw [iteF (ne _ _ (by omega) (by omega) t2)]
    by_cases t1 : t = 1
    · subst t1; rw [iteT rfl]; rfl
    rw [iteF (ne _ _ (by omega) (by omega) t1)]
    by_cases t0 : t = 0
    · subst t0; rw [iteT (by rfl)]; rfl
    rw [iteF (show State.addr b + BitVec.ofNat 64 (BITS + t) ≠ State.addr b + BitVec.ofNat 64 BITS from
      fun e => ne t 0 (by omega) (by omega) t0 (by rw [e]; rfl)), h3.bits t (by omega), hm2,
      iteF (show ¬ t < 3 by omega), iteF t254]
    rfl

end

end VG.Proof.X25519.Arm
