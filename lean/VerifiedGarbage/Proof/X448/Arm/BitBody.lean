import VerifiedGarbage.Proof.X448.Arm.BitWrite

/-!
# X448 on ARMv7: one scalar byte

The public byte counter selects a scalar byte, expands it, and advances the
loop.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm
open VG.Proof.X25519.Arm (wp_dp wp_ldrb wp_cmp op2_reg op2_lsl op2_imm)

def bitHead : List Instr :=
  [.dp .add .r7 .r1 (.reg .r11), .ldrb .r3 .r7 0,
    .dp .add .r7 .r0 (.shifted .r11 .lsl 3)]

def bitTail : List Instr := [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm 56)]

def bitRegs : List Reg := [.r3, .r2, .r11, .r7]

theorem bitHead_ok {s : State} {base k : Addr} (_hs : Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 56 ≤ 2 ^ 32) {i : Nat} (hi : i < 56)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block bitHead) s fun t =>
      t.gpr .r3 = (s.mem (off k i)).setWidth 32 ∧
      t.gpr .r7 = t.gpr .r0 + BitVec.ofNat 32 (8 * i) ∧
      t.mem = s.mem ∧ Keeps [.r3, .r7] s t := by
  unfold bitHead
  refine wp_dp (op2_reg _ _) fun t ht => ?_
  have ea : State.addr (t.gpr .r7 + BitVec.ofNat 32 0) = off k i := by
    rw [ht.gpr]; change State.addr (s.gpr .r1 + s.gpr .r11 + BitVec.ofNat 32 0) = _
    rw [BitVec.add_zero, hb, addr_add (by omega), hk]
  refine wp_ldrb (by decide) ea (by rw [ht.rd, ht.wr]; exact hkr) fun u hu => ?_
  refine wp_dp (op2_lsl (by decide)) fun v hv => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hv.other .r3 (by decide), hu.gpr, ht.mem]
  · rw [hv.gpr, hv.other .r0 (by decide)]
    change u.gpr .r0 + u.gpr .r11 <<< 3 = _
    rw [hu.other .r11 (by decide), ht.other .r11 (by decide), hb]
    apply congrArg (u.gpr .r0 + ·)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  · exact hv.mem.trans (hu.mem.trans ht.mem)
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest (by decide))))

theorem bitTail_ok {s : State} {i : Nat} (hi : i < 56) (hb : s.gpr .r11 = BitVec.ofNat 32 i) :
    WP isa (.block bitTail) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 56) ∧
      t.mem = s.mem ∧ Keeps [.r11] s t := by
  have check : ∀ n < 56,
      ((BitVec.ofNat 32 n + (1 : BitVec 32) - (56 : BitVec 32)) == 0) = decide (n + 1 = 56) :=
    by decide +kernel
  unfold bitTail
  refine wp_dp (op2_imm (by decide)) fun t ht => ?_
  refine wp_cmp (op2_imm (by decide)) fun u hu hz => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hu.gpr, ht.gpr]; change s.gpr .r11 + BitVec.ofNat 32 1 = _
    rw [hb, ← BitVec.ofNat_add]
  · rw [hz, ht.gpr]; change ((s.gpr .r11 + 1 - 56) == 0) = _
    rw [hb]; exact check i hi
  · exact hu.mem.trans ht.mem
  · exact rest_keeps ((ht.rest (by decide)).trans (hu.rest _))

theorem bitsBody_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 56 ≤ 2 ^ 32) {i : Nat} (hi : i < 56)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block bitsBody) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 56) ∧ Keeps bitRegs s t ∧
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (bitHead ++ (List.range 8).flatMap bitJ ++ bitTail)) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (bitHead_ok hs hk hfit hi hb hkr) fun t ⟨ta, tp, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (byteBits_ok (hs.of_keeps tk (by decide)) hi tp ta) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .r11 = BitVec.ofNat 32 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (bitTail_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
  refine ⟨vb, vz, ?_, ?_, ?_⟩
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
  · rw [vm]; exact uf
  · rw [vm, ← tm]; exact um

end VG.Proof.X448.Arm
