import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Hint
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.Proof.MlDsa.Pack.Hint
import VerifiedGarbage.Proof.MlDsa.Pack.Mem
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-!
# ML-DSA on 32-bit ARM: what the proofs of `HintBitPack` and `HintBitUnpack` share

Untrusted: everything here is checked by Lean. The comparisons of small
numbers (`ltBit`), pointers that do not wrap around, the parameters, and the
frames: the words a push stores, which the body and the pop reload.
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm
open VG.Spec.MlDsa

/-! ## Numbers -/

theorem mem_hintParams {ω k : Nat} (h : (ω, k) ∈ hintParams) : 4 ≤ k ∧ k ≤ 8 ∧ 55 ≤ ω ∧ ω ≤ 80 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

/-- The sign bit of `x - y`, for `x` and `y` less than `2³¹`: whether `x < y`. -/
theorem ltBit_val {x y : BitVec 32} (hx : x.toNat < 2 ^ 31) (hy : y.toNat < 2 ^ 31) :
    (x - y) >>> 31 = if x.toNat < y.toNat then 1 else 0 := by
  split <;> bv_omega

/-- `Z` after `ltBit`: set iff `x ≥ y`. -/
theorem ltBit_z {x y : BitVec 32} (hx : x.toNat < 2 ^ 31) (hy : y.toNat < 2 ^ 31) :
    ((x - y) >>> 31 - 0 == 0) = decide (y.toNat ≤ x.toNat) := by
  rw [ltBit_val hx hy]
  split
  · rw [decide_eq_false (by omega)]; rfl
  · rw [decide_eq_true (by omega)]; rfl

theorem sub_zero32 (x : BitVec 32) : x - 0 = x := BitVec.sub_zero x

theorem toNat_ofNat32 {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_succ32 (x : Nat) : BitVec.ofNat 32 x + 1 = BitVec.ofNat 32 (x + 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]

theorem ptr_add (p : BitVec 32) (a b : Nat) : p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- `Z` after comparing a counter with a constant. -/
theorem cmp_const {j c : Nat} (hj : j < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.ofNat 32 j - BitVec.ofNat 32 c == 0) = decide (j = c) := by
  rw [VG.Proof.MlKem.Arm.cmp_z _ _ hc, toNat_ofNat32 hj]

/-- The byte `strb` stores of a small number. -/
theorem setWidth8_ofNat (x : Nat) : (BitVec.ofNat 32 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A byte, as `ldrb` loads it. -/
theorem byte_toNat32 (b : Byte) : (b.setWidth 32).toNat = b.toNat := VG.Proof.MlKem.Arm.setWidth32_toNat b

/-! ## Addresses -/

theorem addr_ofNat (p : BitVec 32) {a : Nat} (h : p.toNat + a < 2 ^ 32) :
    State.addr (p + BitVec.ofNat 32 a) = State.addr p + BitVec.ofNat 64 a := addr_add h

theorem addr_sub' {a : BitVec 32} {k : Nat} (h : k ≤ a.toNat) :
    State.addr (a - BitVec.ofNat 32 k) = State.addr a - BitVec.ofNat 64 k := by
  have := a.isLt
  simp only [State.addr]; bv_omega

/-! ## Frames -/

/-- Word `i` a push stored. -/
theorem storeWords_readW (m : Mem) (a : BitVec 32) (vs : List (BitVec 32)) (h : a.toNat + 4 * vs.length ≤ 2 ^ 32)
    {i : Nat} (hi : i < vs.length) :
    (storeWords m a vs).readW (State.addr (a + BitVec.ofNat 32 (4 * i))) 32 = vs[i] := by
  induction vs generalizing m a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons v vs ih =>
    simp only [List.length_cons] at h hi
    simp only [storeWords]
    cases i with
    | zero =>
      have hf := storeWords_frame (m.writeW (State.addr a) v) (a + 4) vs (by bv_omega)
      rw [show a + BitVec.ofNat 32 (4 * 0) = a by simp, hf.readW (r := ⟨State.addr a, 4⟩)
        (Region.contains_self _ _) (fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          by_cases hv : vs.length = 0
          · intro x _ h2; simp only [Region.Contains, hv] at h2; omega
          rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, addr_ofNat a (by omega)]
          exact Offset.base_disjoint _ (Nat.le_refl 4) (by have := addr_toNat' a; omega)) (by decide),
        Mem.readW_writeW_self32]
      rfl
    | succ j =>
      rw [show a + BitVec.ofNat 32 (4 * (j + 1)) = a + 4 + BitVec.ofNat 32 (4 * j) by
        rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ptr_add]; congr 2; omega]
      exact ih _ _ (by bv_omega) (by omega)

/-- The region of the frame of `rs`. -/
abbrev frameR (s : State) (rs : List Reg) : Region :=
  ⟨State.addr (s.sp - BitVec.ofNat 32 (4 * rs.length)), 4 * rs.length⟩

/-- A push changes memory only in its frame. -/
theorem pushed_frame (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) :
    Frame [frameR s rs] s.mem (pushed rs s).mem := by
  have := storeWords_frame s.mem (s.sp - BitVec.ofNat 32 (4 * rs.length)) (rs.map s.gpr) (by
    rw [List.length_map]; have := s.sp.isLt; bv_omega)
  rwa [List.length_map] at this

/-- The word of register `rs[i]` in the frame. -/
theorem pushed_word (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) {i : Nat}
    (hi : i < rs.length) :
    (pushed rs s).mem.readW (State.addr (s.sp - BitVec.ofNat 32 (4 * rs.length) + BitVec.ofNat 32 (4 * i))) 32 =
      s.gpr rs[i] := by
  have := storeWords_readW s.mem (s.sp - BitVec.ofNat 32 (4 * rs.length)) (rs.map s.gpr) (by
    rw [List.length_map]; have := s.sp.isLt; bv_omega) (i := i) (by rw [List.length_map]; exact hi)
  rw [List.getElem_map] at this
  exact this

/-- The frame of `rs` is the bytes below `sp`. -/
theorem frameR_eq (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) :
    frameR s rs = ⟨State.addr s.sp - BitVec.ofNat 64 (4 * rs.length), 4 * rs.length⟩ := by
  rw [frameR, addr_sub' h]

theorem frameR_contains (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) {i : Nat}
    (hi : i < rs.length) :
    (frameR s rs).Contains (State.addr (s.sp - BitVec.ofNat 32 (4 * rs.length) + BitVec.ofNat 32 (4 * i))) 4 := by
  have := s.sp.isLt
  have e : (s.sp - BitVec.ofNat 32 (4 * rs.length)).toNat = s.sp.toNat - 4 * rs.length := by bv_omega
  rw [addr_ofNat _ (by omega)]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Word `i` of the frame, after the body changed memory only outside it. -/
theorem frame_saved (rs : List Reg) {s : State} (h : 4 * rs.length ≤ s.sp.toNat) {m : Mem} {R : List Region}
    (hf : Frame R (pushed rs s).mem m) (hd : ∀ r ∈ R, (frameR s rs).Disjoint r) {i : Nat} (hi : i < rs.length) :
    m.readW (State.addr ((pushed rs s).sp + BitVec.ofNat 32 (4 * i))) 32 = s.gpr rs[i] := by
  rw [pushed_sp, hf.readW (frameR_contains rs h hi) hd (by decide), pushed_word rs h hi]

end VG.Proof.MlDsa.Arm.Pack.Hint
