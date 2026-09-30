import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintBase

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_unpack`, the steps

Untrusted: everything here is checked by Lean. As on x86-64, the code
follows the fold form of `HintBitUnpack` (`hintBitUnpack_eq`,
`Proof/MlDsa/Pack/Hint.lean`) step by step: while no check has failed, the
words of `h` are the hint of the spec (`HArr`) and `r1` its index; once one
has, `r1` is 256, which skips the rest (`SRel`). Here: the arguments,
zeroing `h`, and one coefficient (`first_ok`, `next_ok`); the loops are in
`HintUnpackLoops.lean`. They run from any state that permits reading `y` and
writing `h` (`MainPre`), so that constant time can narrow the state to those
two regions.
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr)
open VG.Proof.MlKem (bytesAt_length bytesAt_getD bytesAt_eq)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.Arm.Pack.Hint

/-! ## The arguments -/

section
variable (s₀ : State)

/-- `y`, `len`, `ω`, `h` and `hlen`. -/
abbrev uY : BitVec 32 := s₀.gpr .r0
abbrev uL : BitVec 32 := s₀.gpr .r1
abbrev uW : BitVec 32 := s₀.gpr .r2
abbrev uH : BitVec 32 := s₀.gpr .r3
abbrev uHL : BitVec 32 := stackArg s₀ 0
abbrev uω : Nat := (uW s₀).toNat
abbrev uLen : Nat := (uL s₀).toNat
abbrev uk : Nat := uLen s₀ - uω s₀
abbrev uyR : Region := ⟨State.addr (uY s₀), uLen s₀⟩
abbrev uhR : Region := ⟨State.addr (uH s₀), (uHL s₀).toNat * 4⟩
abbrev uargR : Region := ⟨stackArgAddr s₀ 0, 4⟩
/-- The bytes of `y`, as the spec reads them. -/
abbrev uYs : Array Byte := (bytesAt s₀.mem (State.addr (uY s₀)) (uLen s₀)).toArray

end

/-- The precondition, as `sig_pre` states it. -/
structure UPre (s : State) : Prop where
  sp : 16 ≤ s.sp.toNat
  spA : s.sp.toNat + 4 ≤ 2 ^ 32
  rd : s.rd = [uyR s, uargR s]
  wr : s.wr = [uhR s]
  d_yh : (uyR s).Disjoint (uhR s)
  d_ha : (uhR s).Disjoint (uargR s)
  b_y : (⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint (uyR s)
  b_h : (⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint (uhR s)
  b_a : (⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint (uargR s)
  fitY : (uY s).toNat + uLen s ≤ 2 ^ 32
  fitH : (uH s).toNat + (uHL s).toNat * 4 ≤ 2 ^ 32
  par : (uω s, uk s) ∈ hintParams
  ωle : uω s ≤ uLen s
  hlen : (uHL s).toNat = 256 * uk s

theorem ufacts {s₀ : State} (hp : UPre s₀) : 4 ≤ uk s₀ ∧ uk s₀ ≤ 8 ∧ 55 ≤ uω s₀ ∧ uω s₀ ≤ 80 ∧
    uω s₀ + uk s₀ = uLen s₀ ∧ uLen s₀ ≤ 88 := by
  have := mem_hintParams hp.par
  have := hp.ωle
  have e : uk s₀ = uLen s₀ - uω s₀ := rfl
  omega

/-! ## Zeroing `h` -/

theorem zeroPro_ok {s : State} :
    WP isa (.block [.dp .sub .r6 .r1 (.reg .r2), .mov .r4 (.reg .r12), .mov .r12 (.imm 0), .mov .r5 (.reg .r3)])
      s fun s' => s'.gpr .r6 = s.gpr .r1 - s.gpr .r2 ∧ s'.gpr .r4 = s.gpr .r12 ∧ s'.gpr .r12 = 0 ∧
        s'.gpr .r5 = s.gpr .r3 ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r3 = s.gpr .r3 ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block []

theorem zeroStep_ok {s : State} {p c : BitVec 32} (h5 : s.gpr .r5 = p) (h4 : s.gpr .r4 = c)
    (o : InRegions s.wr (State.addr (p + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.str .r12 .r5 0, .dp .add .r5 .r5 (.imm 4), .subs .r4 .r4 (.imm 1)]) s fun s' =>
      s'.gpr .r5 = p + 4 ∧ s'.gpr .r4 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (p + BitVec.ofNat 32 0)) (s.gpr .r12) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r6 = s.gpr .r6 ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h5, h4, o]

theorem zeroEnd_ok {s : State} :
    WP isa (.block [.mov .r1 (.imm 0)]) s fun s' => s'.gpr .r1 = 0 ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r1 → s'.gpr r = s.gpr r := by
  run_block []
  simp only [true_and]; intro r hr; rw [ite_neg' hr]

/-- Zeroing the `hlen` words of `h`, from the entry values of the registers. -/
theorem zero_ok {s₀ : State} (hp : UPre s₀) {s : State} (h0 : s.gpr .r0 = uY s₀) (h1 : s.gpr .r1 = uL s₀)
    (h2 : s.gpr .r2 = uW s₀) (h3 : s.gpr .r3 = uH s₀) (h12 : s.gpr .r12 = uHL s₀) (hwr : uhR s₀ ∈ s.wr) :
    WP isa hbuZero s fun s' => s'.gpr .r0 = uY s₀ ∧ s'.gpr .r1 = 0 ∧ s'.gpr .r2 = uW s₀ ∧
      s'.gpr .r3 = uH s₀ ∧ s'.gpr .r6 = BitVec.ofNat 32 (uk s₀) ∧
      (∀ t < 256 * uk s₀, coeffAt s'.mem (State.addr (uH s₀)) t = 0) ∧
      Frame [uhR s₀] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨hk4, hk8, -, -, hsum, hL88⟩ := ufacts hp
  have fH := hp.fitH
  have hl := hp.hlen
  have hHL := (uHL s₀).isLt
  unfold hbuZero
  refine WP.seq (WP.mono zeroPro_ok fun s₁ ⟨r6₁, r4₁, r12₁, r5₁, r0₁, r2₁, r3₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  refine WP.seq (wp_loop_ne (N := 256 * uk s₀) (fun t s' => s'.gpr .r5 = uH s₀ + BitVec.ofNat 32 (4 * t) ∧
      s'.gpr .r4 = BitVec.ofNat 32 (1 * (256 * uk s₀ - t)) ∧ s'.gpr .r12 = 0 ∧ s'.gpr .r0 = uY s₀ ∧
      s'.gpr .r2 = uW s₀ ∧ s'.gpr .r3 = uH s₀ ∧ s'.gpr .r6 = BitVec.ofNat 32 (uk s₀) ∧
      Frame [uhR s₀] s.mem s'.mem ∧ (∀ u < t, coeffAt s'.mem (State.addr (uH s₀)) u = 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp) (by omega)
    (fun t ht s' ⟨i5, i4, i12, i0, i2, i3, i6, hf, hz, hrd, hwr', hsp⟩ => ?_)
    (fun s₂ ⟨_, _, _, i0, i2, i3, i6, hf, hz, hrd, hwr', hsp⟩ => ?_)
    ⟨by rw [r5₁, h3]; simp, by rw [r4₁, h12, Nat.one_mul, Nat.sub_zero, ← hl, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      r12₁, by rw [r0₁, h0], by rw [r2₁, h2], by rw [r3₁, h3], ?_, by rw [m₁]; exact Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _), rd₁, wr₁, sp₁⟩)
  · have ea : State.addr (uH s₀ + BitVec.ofNat 32 (4 * t) + BitVec.ofNat 32 0) = coeffAddr (State.addr (uH s₀)) t :=
      by rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
    have hin : (uhR s₀).Contains (coeffAddr (State.addr (uH s₀)) t) 4 := Offset.contains_base _ (by omega) (by omega)
    refine WP.mono (zeroStep_ok i5 i4 (by rw [ea, hwr']; exact ⟨_, hwr, hin⟩))
      fun s'' ⟨r5', r4', z', m', r0', r2', r3', r6', r12', rd', wr', sp'⟩ =>
        ⟨⟨by rw [r5', show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ptr_add, Nat.mul_succ],
          by rw [r4']; exact count_sub (k := 1) ht, by rw [r12', i12],
          by rw [r0', i0], by rw [r2', i2], by rw [r3', i3], by rw [r6', i6], ?_, fun u hu => ?_,
          by rw [rd', hrd], by rw [wr', hwr'], by rw [sp', hsp]⟩,
          by rw [z']; exact count_z (k := 1) ht (by decide) (by omega)⟩
    · rw [m', ea]
      exact hf.writeW (List.mem_singleton_self _) _ hin
    · rw [m', ea, i12]
      by_cases e : u = t
      · subst e; rw [coeffAt_eq, Mem.readW_writeW_self32]
      · rw [coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
          ← coeffAt_eq, hz u (by omega)]
  · rw [r6₁, h1, h2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le hp.ωle, toNat_ofNat32 (by omega)]

  · refine WP.mono zeroEnd_ok
      fun s₃ ⟨r1₃, m₃, rd₃, wr₃, sp₃, g₃⟩ => ⟨by rw [g₃ _ (by decide), i0], r1₃, by rw [g₃ _ (by decide), i2],
        by rw [g₃ _ (by decide), i3], by rw [g₃ _ (by decide), i6], by rw [m₃]; exact hz,
        by rw [m₃]; exact hf, by rw [rd₃, hrd], by rw [wr₃, hwr'], by rw [sp₃, hsp]⟩
end VG.Proof.MlDsa.Arm.Pack.Hint.Unpack
