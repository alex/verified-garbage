import VerifiedGarbage.Proof.X25519.Arm.Freeze

/-!
# X25519 on 32-bit ARM: the setup

Untrusted: everything here is checked by Lean. The u-coordinate as 16-bit
limbs (`decode_val`: the number of its 32 bytes modulo `2²⁵⁵`), and the
setup of the working space: the saved registers, `x1 = x3 = u`,
`x2 = z3 = 1`, `z2 = 0` and `a24` (`setup_ok`); the bits of the scalar
(`bits_ok`).
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe bytesAt a24)
open VG.Proof.X25519 (leNum leNum_append bytesAt_add bytesAt_succ length_bytesAt toFe)

/-! ## The u-coordinate as limbs -/

/-- Byte `i` at `p`, as a number. -/
def byteN (m : Mem) (p : Addr) (i : Nat) : Nat := (m (p + BitVec.ofNat 64 i)).toNat

/-- Limb `k` of the decoded u-coordinate: bytes `2k` and `2k + 1`, the top bit
masked. -/
def uLimb (m : Mem) (p : Addr) (k : Nat) : Nat :=
  byteN m p (2 * k) + 256 * (if k = 15 then byteN m p (2 * k + 1) % 128 else byteN m p (2 * k + 1))

theorem leNum_bytesAt2 (m : Mem) (p : Addr) :
    ∀ n, leNum (bytesAt m p (2 * n)) = val16 (fun k => byteN m p (2 * k) + 256 * byteN m p (2 * k + 1)) n
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 2 from rfl, bytesAt_add, leNum_append, leNum_bytesAt2 m p n, val16_succ,
      length_bytesAt, show (256 : Nat) ^ (2 * n) = 2 ^ (16 * n) by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega]
    congr 2
    rw [bytesAt_succ, bytesAt_succ, show bytesAt m (p + BitVec.ofNat 64 (2 * n) + 1 + 1) 0 = [] from rfl]
    simp only [leNum, byteN, Nat.mul_zero, Nat.add_zero]
    rw [Offset.add_ofNat_add_one]

theorem uLimb_lt (m : Mem) (p : Addr) : ∀ k < 16, uLimb m p k < 65536 := by
  intro k _
  have h0 := (m (p + BitVec.ofNat 64 (2 * k))).isLt
  have h1 := (m (p + BitVec.ofNat 64 (2 * k + 1))).isLt
  simp only [uLimb, byteN]
  split <;> omega

/-- The limbs of the decoded u-coordinate. -/
theorem decode_val (m : Mem) (p : Addr) :
    val16 (uLimb m p) 16 = VG.Spec.X25519.decodeUCoordinate (bytesAt m p 32) := by
  rw [VG.Proof.X25519.decodeUCoordinate_eq (length_bytesAt m p 32), show 32 = 2 * 16 from rfl,
    leNum_bytesAt2]
  have e : val16 (uLimb m p) 15 = val16 (fun k => byteN m p (2 * k) + 256 * byteN m p (2 * k + 1)) 15 :=
    val16_congr fun k hk => by simp [uLimb, show k ≠ 15 by omega]
  have hlo := val16_lt (f := uLimb m p) (n := 15) fun k hk => uLimb_lt m p k (by omega)
  rw [show 16 * 15 = 240 from rfl] at hlo
  rw [val16_succ (uLimb m p) 15, val16_succ (fun k => byteN m p (2 * k) + 256 * byteN m p (2 * k + 1)) 15,
    ← e, show 16 * 15 = 240 from rfl]
  simp only [uLimb, ite_true, show 2 * 15 = 30 from rfl, show 2 * 15 + 1 = 31 from rfl]
  have h31 := (m (p + BitVec.ofNat 64 31)).isLt
  have h30 := (m (p + BitVec.ofNat 64 30)).isLt
  simp only [byteN] at *
  generalize (m (p + BitVec.ofNat 64 31)).toNat = x at *
  generalize (m (p + BitVec.ofNat 64 30)).toNat = y at *
  generalize val16 (uLimb m p) 15 = L at *
  have hx : x = x % 128 + 128 * (x / 128) := (Nat.mod_add_div _ _).symm
  have hlt : L + 2 ^ 240 * (y + 256 * (x % 128)) < 2 ^ 255 := by
    have : 2 ^ 240 * (y + 256 * (x % 128)) ≤ 2 ^ 240 * 32767 :=
      Nat.mul_le_mul_left _ (by have := Nat.mod_lt x (show 128 > 0 by decide); omega)
    rw [show (2 : Nat) ^ 255 = 2 ^ 240 * 32768 from rfl]; omega
  rw [show L + 2 ^ 240 * (y + 256 * x) = L + 2 ^ 240 * (y + 256 * (x % 128)) + 2 ^ 255 * (x / 128) by
    conv => lhs; rw [hx]
    rw [show (2 : Nat) ^ 255 = 2 ^ 240 * 32768 from rfl]
    rw [Nat.mul_add 256, Nat.mul_add (2 ^ 240), Nat.mul_add (2 ^ 240), Nat.mul_assoc (2 ^ 240) 32768]
    omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-! ## Saving the registers -/

/-- The registers `g` saved at `[0, 32)` of the working space at `B`. -/
def Saved (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (B + BitVec.ofNat 64 (4 * i)) 32 = g (savedReg i)

section
variable {b : BitVec 32}

theorem saves_ok {s : State} (h3 : s.gpr .r3 = b) (hfit : b.toNat + 4096 ≤ 2 ^ 32)
    (hw : (⟨State.addr b, 4096⟩ : Region) ∈ s.wr) :
    WP isa (.block ((List.range 8).flatMap fun i => [.str (savedReg i) .r3 (4 * i)])) s fun s' =>
      Saved (State.addr b) s.gpr s'.mem ∧ Frame [⟨State.addr b, 32⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧
        Rest [] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.mem.readW (State.addr b + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (savedReg i)) ∧
      Frame [⟨State.addr b, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun n s' hn ⟨h1, h2, h3', h4⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩)
    fun s' h => ⟨h.1, h.2.1, h.2.2⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * n)) (by omega)
    (by rw [h3', h3]; exact addr_add (by omega)) (by rw [h4.wr]; exact in_base hw (by omega) (by omega))
    fun s2 u2 => WP.block_nil ⟨fun i hi => ?_, ?_, by rw [u2.gpr, h3'], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h1 i hi
    · rw [Mem.readW_writeW_self32, h3']
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-! ## Decoding the u-coordinate -/

theorem toNat_setWidth8 (x : BitVec 8) : (x.setWidth 32).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem decodeStep_ok {k : Nat} (hk : k < 16) {s : State} (hc : Ctx b s) {pt : BitVec 32}
    (h2 : s.gpr .r2 = pt) (hpf : pt.toNat + 32 ≤ 2 ^ 32)
    (hin : (⟨State.addr pt, 32⟩ : Region) ∈ s.rd ++ s.wr) :
    WP isa (.block (decodeStep k)) s fun s' =>
      wd s'.mem (State.addr b) (X1 + 4 * k) = uLimb s.mem (State.addr pt) k ∧
      wd s'.mem (State.addr b) (X3 + 4 * k) = uLimb s.mem (State.addr pt) k ∧
      s'.mem = (s.mem.writeW (State.addr b + BitVec.ofNat 64 (X1 + 4 * k)) (BitVec.ofNat 32 (uLimb s.mem (State.addr pt) k))).writeW
        (State.addr b + BitVec.ofNat 64 (X3 + 4 * k)) (BitVec.ofNat 32 (uLimb s.mem (State.addr pt) k)) ∧
      Rest [.r4, .r5] s s' := by
  have hX1 : X1 = 64 := rfl
  have hX3 : X3 = 256 := rfl
  have hin' : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr pt + BitVec.ofNat 64 i) 1 := fun i hi =>
    in_base hin (by omega) (by omega)
  have hlt := uLimb_lt s.mem (State.addr pt) k hk
  have hb0 : byteN s.mem (State.addr pt) (2 * k) < 256 := (s.mem (State.addr pt + BitVec.ofNat 64 (2 * k))).isLt
  have hb1 : byteN s.mem (State.addr pt) (2 * k + 1) < 256 :=
    (s.mem (State.addr pt + BitVec.ofNat 64 (2 * k + 1))).isLt
  -- The two bytes, then (for limb 15) the mask, then the limb.
  have key : ∀ (is : List Instr) (s2 : State), Rest [.r4, .r5] s s2 → s2.mem = s.mem →
      (s2.gpr .r4).toNat = byteN s.mem (State.addr pt) (2 * k) →
      (s2.gpr .r5).toNat = (if k = 15 then byteN s.mem (State.addr pt) (2 * k + 1) % 128
        else byteN s.mem (State.addr pt) (2 * k + 1)) →
      is = [.dp .add .r4 .r4 (.shifted .r5 .lsl 8), .str .r4 .r0 (X1 + 4 * k), .str .r4 .r0 (X3 + 4 * k)] →
      WP isa (.block is) s2 fun s' =>
        wd s'.mem (State.addr b) (X1 + 4 * k) = uLimb s.mem (State.addr pt) k ∧
        wd s'.mem (State.addr b) (X3 + 4 * k) = uLimb s.mem (State.addr pt) k ∧
        s'.mem = (s.mem.writeW (State.addr b + BitVec.ofNat 64 (X1 + 4 * k))
          (BitVec.ofNat 32 (uLimb s.mem (State.addr pt) k))).writeW
          (State.addr b + BitVec.ofNat 64 (X3 + 4 * k)) (BitVec.ofNat 32 (uLimb s.mem (State.addr pt) k)) ∧
        Rest [.r4, .r5] s s' := by
    intro is s2 hr2 hm2 e4 e5 his
    subst his
    have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
    refine wp_dp (op2_lsl (by decide)) fun s3 u3 => ?_
    have ev : s3.gpr .r4 = BitVec.ofNat 32 (uLimb s.mem (State.addr pt) k) := by
      apply BitVec.eq_of_toNat_eq
      rw [u3.gpr]
      show (s2.gpr .r4 + s2.gpr .r5 <<< 8).toNat = _
      have h5 : (s2.gpr .r5).toNat < 256 := by rw [e5]; split <;> omega
      have h5' : (s2.gpr .r5).toNat * 2 ^ 8 % 2 ^ 32 = (s2.gpr .r5).toNat * 256 := Nat.mod_eq_of_lt (by omega)
      rw [toNat_add_lt (by rw [toNat_shl, h5', e4]; omega), toNat_shl, h5', e4, toNat_imm (by omega), uLimb,
        ← e5]
      omega
    have hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := [.r4]) (by decide)) (by decide)
    refine str0_ok hc3 (d := X1 + 4 * k) (by omega) fun s4 u4 => ?_
    refine str0_ok (hc3.of_rest (u4.rest []) (by decide)) (d := X3 + 4 * k) (by omega) fun s5 u5 =>
      WP.block_nil ⟨?_, ?_, ?_, hr2.trans ((u3.rest (by decide)).trans ((u4.rest _).trans (u5.rest _)))⟩
    · rw [u5.mem, wd_write_other _ _ _ (by omega) (by omega) (by omega), u4.mem, wd_write_self, ev,
        toNat_imm (by omega)]
    · rw [u5.mem, wd_write_self, u4.gpr, ev, toNat_imm (by omega)]
    · rw [u5.mem, u4.gpr, u4.mem, u3.mem, hm2, ev]
  have e0 : State.addr (s.gpr .r2 + BitVec.ofNat 32 (2 * k)) = State.addr pt + BitVec.ofNat 64 (2 * k) := by
    rw [h2]; exact addr_add (by omega)
  have e1 : State.addr (s.gpr .r2 + BitVec.ofNat 32 (2 * k + 1)) =
      State.addr pt + BitVec.ofNat 64 (2 * k + 1) := by
    rw [h2]; exact addr_add (by omega)
  unfold decodeStep
  refine wp_ldrb (a := State.addr pt + BitVec.ofNat 64 (2 * k)) (by omega) e0 (hin' _ (by omega))
    fun s1 u1 => ?_
  refine wp_ldrb (a := State.addr pt + BitVec.ofNat 64 (2 * k + 1)) (by omega)
    (by rw [u1.other .r2 (by decide)]; exact e1) (by rw [u1.rd, u1.wr]; exact hin' _ (by omega)) fun s2 u2 => ?_
  have e4 : (s2.gpr .r4).toNat = byteN s.mem (State.addr pt) (2 * k) := by
    rw [u2.other _ (by decide), u1.gpr, toNat_setWidth8]; rfl
  have e5 : (s2.gpr .r5).toNat = byteN s.mem (State.addr pt) (2 * k + 1) := by
    rw [u2.gpr, u1.mem, toNat_setWidth8]; rfl
  have hr2 : Rest [.r4, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  by_cases h15 : k = 15
  · simp only [h15, ite_true]
    refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
    subst h15
    refine key _ s3 (hr2.trans (u3.rest (by decide))) (by rw [u3.mem, hm2])
      (by rw [u3.other _ (by decide), e4]) ?_ rfl
    rw [u3.gpr]
    show (s2.gpr .r5 &&& 127).toNat = _
    rw [BitVec.toNat_and, e5, show (127 : BitVec 32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    rfl
  · simp only [h15, ite_false]
    exact key _ s2 hr2 hm2 e4 (by rw [e5, iteF h15]) rfl

/-- A word outside a range that code wrote. -/
theorem wd_keep {m m' : Mem} {B : Addr} {o n d : Nat} (hf : Frame [⟨B + BitVec.ofNat 64 o, n⟩] m m')
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hb : d + 4 ≤ 4096) (ho : o + n ≤ 4096) : wd m' B d = wd m B d :=
  wd_frame hf fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd (by omega) (by omega)

theorem decode_ok {s0 : State} (hc : Ctx b s0) {pt : BitVec 32} (h2 : s0.gpr .r2 = pt)
    (hpf : pt.toNat + 32 ≤ 2 ^ 32) (hin : (⟨State.addr pt, 32⟩ : Region) ∈ s0.rd ++ s0.wr)
    (hd : Region.Disjoint ⟨State.addr pt, 32⟩ ⟨State.addr b, 4096⟩) :
    WP isa (.block ((List.range 16).flatMap decodeStep)) s0 fun s' =>
      (∀ k < 16, limb s'.mem (State.addr b) X1 k = uLimb s0.mem (State.addr pt) k ∧
        limb s'.mem (State.addr b) X3 k = uLimb s0.mem (State.addr pt) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 X1, 256⟩] s0.mem s'.mem ∧ Rest [.r4, .r5] s0 s' := by
  have hX1 : X1 = 64 := rfl
  have hX3 : X3 = 256 := rfl
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s => (∀ k < n, limb s.mem (State.addr b) X1 k = uLimb s0.mem (State.addr pt) k ∧
        limb s.mem (State.addr b) X3 k = uLimb s0.mem (State.addr pt) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 X1, 256⟩] s0.mem s.mem ∧ Rest [.r4, .r5] s0 s)
    (fun k s hk ⟨h1, hf, hr⟩ => ?_) 16 (Nat.le_refl _) s0
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Rest.refl _ _⟩) fun s' h => h
  have hcs : Ctx b s := hc.of_rest hr (by decide)
  refine WP.mono (decodeStep_ok hk hcs (pt := pt) (by rw [hr.gpr _ (by decide), h2]) hpf
    (by rw [hr.rd, hr.wr]; exact hin)) fun s' ⟨e1, e3, hm, hr'⟩ => ⟨fun j hj => ?_, ?_, hr.trans hr'⟩
  · -- The bytes of the u-coordinate are as in `s0`.
    have hu : uLimb s.mem (State.addr pt) k = uLimb s0.mem (State.addr pt) k := by
      have hby : ∀ i < 32, s.mem (State.addr pt + BitVec.ofNat 64 i) = s0.mem (State.addr pt + BitVec.ofNat 64 i) :=
        fun i hi => hf _ fun r hr' => by
          rw [List.mem_singleton.mp hr'] at *
          intro hcon
          exact hd _ (Offset.contains_base _ (by omega) (by omega))
            ((Offset.sub_base (State.addr b) (d := X1) (n := 256) (k := 4096) (by omega)) _ hcon)
      simp only [uLimb, byteN, hby (2 * k) (by omega), hby (2 * k + 1) (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [limb, limb, hm, wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h1 j hj
    · rw [limb, limb, e1, e3, hu]; exact ⟨rfl, rfl⟩
  · rw [hm]
    exact (hf.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

/-- The ranges `consts` writes. -/
abbrev constsR (b : BitVec 32) : List Region :=
  [⟨State.addr b + BitVec.ofNat 64 X2, 128⟩, ⟨State.addr b + BitVec.ofNat 64 Z3, 64⟩,
    ⟨State.addr b + BitVec.ofNat 64 A24, 64⟩]

theorem constsR_sub (e k o n : Nat) (he : (⟨State.addr b + BitVec.ofNat 64 e, k⟩ : Region) ∈ constsR b)
    (h1 : e ≤ o) (h2 : o + n ≤ e + k) : ∃ r ∈ constsR b, Region.Sub ⟨State.addr b + BitVec.ofNat 64 o, n⟩ r :=
  ⟨_, he, Offset.sub (State.addr b) h1 h2⟩

theorem consts_ok {s : State} (hc : Ctx b s) :
    WP isa (.block consts) s fun s' =>
      (∀ k < 16, limb s'.mem (State.addr b) X2 k = if k = 0 then 1 else 0) ∧
      (∀ k < 16, limb s'.mem (State.addr b) Z2 k = 0) ∧
      (∀ k < 16, limb s'.mem (State.addr b) Z3 k = if k = 0 then 1 else 0) ∧
      (∀ k < 16, limb s'.mem (State.addr b) A24 k = if k = 0 then 56129 else if k = 1 then 1 else 0) ∧
      Frame (constsR b) s.mem s'.mem ∧ Rest [.r4, .r5, .r6] s s' := by
  have hX2 : X2 = 128 := rfl
  have hZ2 : Z2 = 192 := rfl
  have hZ3 : Z3 = 320 := rfl
  have hA : A24 = 960 := rfl
  simp only [consts, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 =>
    wp_movw fun s3 u3 => ?_
  have hr3 : Rest [.r4, .r5, .r6] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  have g4 : s3.gpr .r4 = 1 := by rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
  have g5 : s3.gpr .r5 = 0 := by rw [u3.other _ (by decide), u2.gpr]
  have g6 : (s3.gpr .r6).toNat = 56129 := by rw [u3.gpr]; rfl
  refine str0_ok hc3 (d := X2) (by omega) fun s4 u4 => ?_
  refine str0_ok (hc3.of_rest (u4.rest []) (by decide)) (d := Z2) (by omega) fun s5 u5 => ?_
  refine str0_ok (hc3.of_rest ((u4.rest []).trans (u5.rest [])) (by decide)) (d := Z3) (by omega)
    fun s6 u6 => ?_
  have hr6 : Rest [] s3 s6 := (u4.rest []).trans ((u5.rest []).trans (u6.rest []))
  refine str0_ok (hc3.of_rest hr6 (by decide)) (d := A24) (by omega) fun s7 u7 => ?_
  refine str0_ok (hc3.of_rest (hr6.trans (u7.rest [])) (by decide)) (d := A24 + 4) (by omega) fun s8 u8 => ?_
  have hr8 : Rest [] s3 s8 := hr6.trans ((u7.rest []).trans (u8.rest []))
  have hc8 : Ctx b s8 := hc3.of_rest hr8 (by decide)
  have hg8 : ∀ r, s8.gpr r = s3.gpr r := fun r => hr8.gpr r (by simp)
  have hm8 : s8.mem = ((((s3.mem.writeW (State.addr b + BitVec.ofNat 64 X2) (s3.gpr .r4)).writeW
      (State.addr b + BitVec.ofNat 64 Z2) (s3.gpr .r5)).writeW (State.addr b + BitVec.ofNat 64 Z3) (s3.gpr .r4)).writeW
      (State.addr b + BitVec.ofNat 64 A24) (s3.gpr .r6)).writeW (State.addr b + BitVec.ofNat 64 (A24 + 4)) (s3.gpr .r4) := by
    rw [u8.mem, u7.gpr, u7.mem, u6.gpr, u6.mem, u5.gpr, u5.mem, u4.gpr, u4.mem]
  refine WP.append (stores_ok (r := .r5) (o := X2 + 4) (n := 15) (by omega) hc8) fun s9 ⟨w9, f9, g9, r9⟩ => ?_
  have hc9 : Ctx b s9 := hc8.of_rest r9 (by decide)
  refine WP.append (stores_ok (r := .r5) (o := Z2 + 4) (n := 15) (by omega) hc9) fun s10 ⟨w10, f10, g10, r10⟩ => ?_
  have hc10 : Ctx b s10 := hc9.of_rest r10 (by decide)
  refine WP.append (stores_ok (r := .r5) (o := Z3 + 4) (n := 15) (by omega) hc10)
    fun s11 ⟨w11, f11, g11, r11⟩ => ?_
  have hc11 : Ctx b s11 := hc10.of_rest r11 (by decide)
  refine WP.mono (stores_ok (r := .r5) (o := A24 + 8) (n := 14) (by omega) hc11)
    fun s12 ⟨w12, f12, g12, r12⟩ => ?_
  have e5 : ∀ t : State, t.gpr = s8.gpr → (t.gpr .r5).toNat = 0 := fun t ht => by rw [ht, hg8, g5]; rfl
  -- Words written by the first stores, through the later ones.
  have k8 : ∀ d, d + 4 ≤ 4096 → (d + 4 ≤ X2 + 4 ∨ X2 + 64 ≤ d) → (d + 4 ≤ Z2 + 4 ∨ Z2 + 64 ≤ d) →
      (d + 4 ≤ Z3 + 4 ∨ Z3 + 64 ≤ d) → (d + 4 ≤ A24 + 8 ∨ A24 + 64 ≤ d) →
      wd s12.mem (State.addr b) d = wd s8.mem (State.addr b) d := fun d hd h1 h2 h3 h4 => by
    rw [wd_keep f12 h4 hd (by omega), wd_keep f11 h3 hd (by omega), wd_keep f10 h2 hd (by omega),
      wd_keep f9 h1 hd (by omega)]
  have g9' : s9.gpr = s8.gpr := g9
  have g10' : s10.gpr = s8.gpr := g10.trans g9
  have g11' : s11.gpr = s8.gpr := g11.trans g10'
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [limb, Nat.mul_zero, Nat.add_zero, k8 _ (by omega) (by omega) (by omega) (by omega) (by omega), hm8,
        wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_self, g4]; rfl
    · rw [limb, wd_keep f12 (by omega) (by omega) (by omega), wd_keep f11 (by omega) (by omega) (by omega),
        wd_keep f10 (by omega) (by omega) (by omega), show X2 + 4 * k = X2 + 4 + 4 * (k - 1) by omega,
        w9 (k - 1) (by omega), e5 _ rfl]
      simp only [show k ≠ 0 by omega, ite_false]
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [limb, Nat.mul_zero, Nat.add_zero, k8 _ (by omega) (by omega) (by omega) (by omega) (by omega), hm8,
        wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_self, g5]; rfl
    · rw [limb, wd_keep f12 (by omega) (by omega) (by omega), wd_keep f11 (by omega) (by omega) (by omega),
        show Z2 + 4 * k = Z2 + 4 + 4 * (k - 1) by omega, w10 (k - 1) (by omega), e5 _ g9']
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [limb, Nat.mul_zero, Nat.add_zero, k8 _ (by omega) (by omega) (by omega) (by omega) (by omega), hm8,
        wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_self, g4]; rfl
    · rw [limb, wd_keep f12 (by omega) (by omega) (by omega), show Z3 + 4 * k = Z3 + 4 + 4 * (k - 1) by omega,
        w11 (k - 1) (by omega), e5 _ g10']
      simp only [show k ≠ 0 by omega, ite_false]
  · rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk2 with hk1 | rfl
      · rw [show k = 0 by omega, limb, Nat.mul_zero, Nat.add_zero,
          k8 _ (by omega) (by omega) (by omega) (by omega) (by omega), hm8,
          wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_self, g6]; rfl
      · rw [limb, k8 _ (by omega) (by omega) (by omega) (by omega) (by omega), hm8,
          show A24 + 4 * 1 = A24 + 4 from rfl, wd_write_self, g4]; rfl
    · rw [limb, show A24 + 4 * k = A24 + 8 + 4 * (k - 2) by omega, w12 (k - 2) (by omega), e5 _ g11']
      simp only [show k ≠ 0 by omega, show k ≠ 1 by omega, ite_false]
  · -- Every write is in `constsR`.
    have m1 : (⟨State.addr b + BitVec.ofNat 64 X2, 128⟩ : Region) ∈ constsR b := List.mem_cons_self ..
    have m2 : (⟨State.addr b + BitVec.ofNat 64 Z3, 64⟩ : Region) ∈ constsR b :=
      List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have m3 : (⟨State.addr b + BitVec.ofNat 64 A24, 64⟩ : Region) ∈ constsR b :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have f8 : Frame (constsR b) s.mem s8.mem := by
      rw [hm8, u3.mem, u2.mem, u1.mem]
      exact (((((Frame.refl _ _).writeW m1 (s3.gpr .r4) (Offset.contains _ (d := X2) (n := 4) (by omega) (by omega)
        (by omega))).writeW m1 (s3.gpr .r5) (Offset.contains _ (d := Z2) (n := 4) (by omega) (by omega)
        (by omega))).writeW m2 (s3.gpr .r4) (Offset.contains _ (d := Z3) (n := 4) (by omega) (by omega)
        (by omega))).writeW m3 (s3.gpr .r6) (Offset.contains _ (d := A24) (n := 4) (by omega) (by omega)
        (by omega))).writeW m3 (s3.gpr .r4) (Offset.contains _ (d := A24 + 4) (n := 4) (by omega) (by omega)
        (by omega))
    exact f8.trans ((f9.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact constsR_sub _ _ _ _ m1 (by omega) (by omega)).trans
      ((f10.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact constsR_sub _ _ _ _ m1 (by omega) (by omega)).trans
      ((f11.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact constsR_sub _ _ _ _ m2 (by omega) (by omega)).trans
      (f12.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact constsR_sub _ _ _ _ m3 (by omega) (by omega)))))
  · exact hr3.trans ((hr8.mono (by decide)).trans ((r9.mono (by decide)).trans ((r10.mono (by decide)).trans
      ((r11.mono (by decide)).trans (r12.mono (by decide))))))

end

/-! ## The whole setup -/

/-- The precondition of `vg_x25519(out = r0, scalar = r1, point = r2, scratch = r3)`, by field. -/
structure XPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 32⟩, ⟨State.addr (s.gpr .r2), 32⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r3), 4096⟩]
  out_sc : Region.Disjoint ⟨State.addr (s.gpr .r0), 32⟩ ⟨State.addr (s.gpr .r1), 32⟩
  out_pt : Region.Disjoint ⟨State.addr (s.gpr .r0), 32⟩ ⟨State.addr (s.gpr .r2), 32⟩
  out_ws : Region.Disjoint ⟨State.addr (s.gpr .r0), 32⟩ ⟨State.addr (s.gpr .r3), 4096⟩
  sc_ws : Region.Disjoint ⟨State.addr (s.gpr .r1), 32⟩ ⟨State.addr (s.gpr .r3), 4096⟩
  pt_ws : Region.Disjoint ⟨State.addr (s.gpr .r2), 32⟩ ⟨State.addr (s.gpr .r3), 4096⟩
  f0 : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 32 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 32 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 4096 ≤ 2 ^ 32

/-- The u-coordinate, decoded. -/
def uOf (s : State) : Fe :=
  toFe (VG.Spec.X25519.decodeUCoordinate (bytesAt s.mem (State.addr (s.gpr .r2)) 32))

theorem val16_one : val16 (fun k => if k = 0 then 1 else 0) 16 = 1 := by decide
theorem val16_zero16 : val16 (fun _ => 0) 16 = 0 := by decide
theorem val16_a24 : val16 (fun k => if k = 0 then 56129 else if k = 1 then 1 else 0) 16 = 121665 := by decide

theorem slot_of {m : Mem} {B : Addr} {o : Nat} {f : Nat → Nat} (h : ∀ k < 16, limb m B o k = f k)
    (hf : ∀ k < 16, f k < 65536) : Lim m B o ∧ FS m B o = toFe (val16 f 16) :=
  ⟨fun k hk => by rw [h k hk]; exact hf k hk, by rw [FS, V, val16_congr h]⟩

theorem setup_ok {s : State} (hp : XPre s) :
    WP isa (.block setup) s fun s' =>
      Ctx (s.gpr .r3) s' ∧ s'.gpr .r12 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧
      Saved (State.addr (s.gpr .r3)) s.gpr s'.mem ∧
      Frame [⟨State.addr (s.gpr .r3), 4096⟩] s.mem s'.mem ∧
      SlotsOk s'.mem (State.addr (s.gpr .r3)) LQ (ladV (uOf s) (VG.Proof.X25519.init (uOf s))) ∧
      Rest [.r0, .r4, .r5, .r6, .r12] s s' := by
  have hX1 : X1 = 64 := rfl
  have hX2 : X2 = 128 := rfl
  have hZ2 : Z2 = 192 := rfl
  have hX3 : X3 = 256 := rfl
  have hZ3 : Z3 = 320 := rfl
  have hA : A24 = 960 := rfl
  have hws : (⟨State.addr (s.gpr .r3), 4096⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  simp only [setup, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (saves_ok rfl hp.f3 hws) fun s1 ⟨hsv, hf1, hg1, hr1⟩ => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => wp_mov (op2_reg _ _) fun s3 u3 => ?_
  have hr3 : Rest [.r0, .r12] s s3 := (hr1.mono (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hc3 : Ctx (s.gpr .r3) s3 :=
    ⟨by rw [u3.gpr, u2.other _ (by decide), hg1], hp.f3, by rw [hr3.wr]; exact hws⟩
  have hm3 : s3.mem = s1.mem := by rw [u3.mem, u2.mem]
  refine WP.append (decode_ok hc3 (pt := s.gpr .r2) (by rw [hr3.gpr _ (by decide)]) hp.f2
    (by rw [hr3.rd, hp.rd]; simp) hp.pt_ws) fun s4 ⟨hl4, hf4, hr4⟩ => ?_
  have hc4 : Ctx (s.gpr .r3) s4 := hc3.of_rest hr4 (by decide)
  refine WP.mono (consts_ok hc4) fun s5 ⟨hx2, hz2, hz3, ha24, hf5, hr5⟩ => ?_
  -- The u-coordinate's bytes did not change.
  have hu : ∀ k < 16, uLimb s3.mem (State.addr (s.gpr .r2)) k = uLimb s.mem (State.addr (s.gpr .r2)) k := by
    intro k hk
    have hby : ∀ i < 32, s3.mem (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) =
        s.mem (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) := fun i hi => by
      rw [hm3]
      refine hf1 _ fun r hr hcon => ?_
      rw [List.mem_singleton.mp hr] at hcon
      exact hp.pt_ws _ (Offset.contains_base _ (by omega) (by omega))
        ((Region.sub_prefix (base := State.addr (s.gpr .r3)) (len := 32) (len' := 4096) (by omega)) _ hcon)
    simp only [uLimb, byteN, hby (2 * k) (by omega), hby (2 * k + 1) (by omega)]
  -- `x1` and `x3` through the constants.
  have hkeep : ∀ o, (o = X1 ∨ o = X3) → ∀ k < 16,
      limb s5.mem (State.addr (s.gpr .r3)) o k = uLimb s.mem (State.addr (s.gpr .r2)) k := by
    intro o ho k hk
    have e := limb_frame (o := o) hf5 fun r hr j hj => by
      simp only [constsR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)
    rw [e k hk, ← hu k hk]
    rcases ho with rfl | rfl
    · exact (hl4 k hk).1
    · exact (hl4 k hk).2
  refine ⟨hc4.of_rest hr5 (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr5.gpr _ (by decide), hr4.gpr _ (by decide), u3.other _ (by decide), u2.gpr, hg1]
  · rw [hr5.gpr _ (by decide), hr4.gpr _ (by decide), u3.other _ (by decide), u2.other _ (by decide), hg1]
  · intro i hi
    rw [← hsv i hi, ← hm3]
    have hd : ∀ (rs : List Region), (∀ r ∈ rs, ∃ o n, r = ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 o, n⟩ ∧
        32 ≤ o ∧ o + n ≤ 4096) → ∀ r ∈ rs,
        (⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint r := fun rs h r hr => by
      obtain ⟨o, n, rfl, h1, h2⟩ := h r hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    rw [hf5.readW (Region.contains_self _ _) (hd _ fun r hr => by
        simp only [constsR, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨X2, 128, rfl, by omega, by omega⟩
        · exact ⟨Z3, 64, rfl, by omega, by omega⟩
        · exact ⟨A24, 64, rfl, by omega, by omega⟩) (by decide),
      hf4.readW (Region.contains_self _ _) (hd _ fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨X1, 256, rfl, by omega, by omega⟩) (by decide)]
  · have hsub : ∀ o n, o + n ≤ 4096 → Region.Sub ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 o, n⟩
        ⟨State.addr (s.gpr .r3), 4096⟩ := fun o n h => Offset.sub_base _ h
    refine (hf1.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).trans ?_
    rw [← hm3]
    refine (hf4.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact hsub _ _ (by omega)⟩).trans ?_
    refine hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [constsR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hsub _ _ (by omega)
  · intro q hq
    simp only [LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨h1, h2⟩ := slot_of (hkeep _ (.inl rfl)) (uLimb_lt _ _)
      refine ⟨h1, ?_⟩
      rw [h2, decode_val]; simp only [ladV, ite_true]; rfl
    · obtain ⟨h1, h2⟩ := slot_of hx2 (fun k _ => by split <;> decide)
      refine ⟨h1, ?_⟩
      rw [h2, val16_one]; simp only [ladV, VG.Proof.X25519.init, iteF (show X2 ≠ X1 by decide), ite_true]; rfl
    · obtain ⟨h1, h2⟩ := slot_of hz2 (fun k _ => by decide)
      refine ⟨h1, ?_⟩
      rw [h2, val16_zero16]
      simp only [ladV, VG.Proof.X25519.init, iteF (show Z2 ≠ X1 by decide), iteF (show Z2 ≠ X2 by decide),
        ite_true]; rfl
    · obtain ⟨h1, h2⟩ := slot_of (hkeep _ (.inr rfl)) (uLimb_lt _ _)
      refine ⟨h1, ?_⟩
      rw [h2, decode_val]
      simp only [ladV, VG.Proof.X25519.init, iteF (show X3 ≠ X1 by decide), iteF (show X3 ≠ X2 by decide),
        iteF (show X3 ≠ Z2 by decide), ite_true]; rfl
    · obtain ⟨h1, h2⟩ := slot_of hz3 (fun k _ => by split <;> decide)
      refine ⟨h1, ?_⟩
      rw [h2, val16_one]
      simp only [ladV, VG.Proof.X25519.init, iteF (show Z3 ≠ X1 by decide), iteF (show Z3 ≠ X2 by decide),
        iteF (show Z3 ≠ Z2 by decide), iteF (show Z3 ≠ X3 by decide), ite_true]; rfl
    · obtain ⟨h1, h2⟩ := slot_of ha24 (fun k _ => by split <;> [decide; split <;> decide])
      refine ⟨h1, ?_⟩
      rw [h2, val16_a24]
      simp only [ladV, iteF (show A24 ≠ X1 by decide), iteF (show A24 ≠ X2 by decide),
        iteF (show A24 ≠ Z2 by decide), iteF (show A24 ≠ X3 by decide), iteF (show A24 ≠ Z3 by decide)]; rfl
  · exact (hr3.mono (by decide)).trans ((hr4.mono (by decide)).trans (hr5.mono (by decide)))

end VG.Proof.X25519.Arm
