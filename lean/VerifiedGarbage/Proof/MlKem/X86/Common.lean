import VerifiedGarbage.Proof.MlKem.X86.Leaf
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-KEM on x86 (32-bit): common lemmas

Untrusted: everything here is checked by Lean. Addresses of coefficients
and bytes at a 32-bit pointer, the states a straight-line block leaves
(`Only`), and the arithmetic of `condSub`.
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-! ## Numbers -/

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem toNat_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

theorem eq_ofNat_of_toNat {x : BitVec 32} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 32 n := by
  subst h; simp

/-- `condSub` as the code computes it: `x - q`, plus `q` masked by the borrow. -/
theorem condSub_bv (x d : BitVec 32) (hx : x.toNat < 2 * q) :
    (x - Q + ((d - d - (BitVec.ofBool (decide (x.toNat < Q.toNat))).setWidth 32) &&& Q)).toNat =
      condSub x.toNat := by
  have hq : Q.toNat = 3329 := rfl
  rw [hq]
  unfold condSub
  rw [q_eq] at hx ⊢
  by_cases h : x.toNat < 3329
  · rw [ite_eq_right (by omega), decide_eq_true h]
    have e : (d - d - (BitVec.ofBool true).setWidth 32) &&& Q = Q := by
      rw [BitVec.sub_self]; decide
    rw [e, BitVec.sub_add_cancel]
  · rw [ite_eq_left (by omega), decide_eq_false h]
    have e : (d - d - (BitVec.ofBool false).setWidth 32) &&& Q = 0 := by
      rw [BitVec.sub_self]; decide
    rw [e]; unfold Q; bv_omega

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem ofNat_sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  rw [show BitVec.ofNat 32 a = BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem ofNat_add_ofNat (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem add_ofNat_add (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ofNat_add_ofNat]

/-- A pointer advanced by `d`. -/
theorem ptr_next (x : BitVec 32) (k d : Nat) :
    x + BitVec.ofNat 32 (d * k) + BitVec.ofNat 32 d = x + BitVec.ofNat 32 (d * (k + 1)) := by
  rw [add_ofNat_add, Nat.mul_succ]

/-- A counter counted down. -/
theorem cnt_next {N k : Nat} (hk : k < N) :
    BitVec.ofNat 32 (N - k) - 1 = BitVec.ofNat 32 (N - (k + 1)) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_sub_ofNat (by omega)]
  congr 1

/-- The loop condition after counting down. -/
theorem cnt_ne {N k : Nat} (hk : k < N) (hN : N < 2 ^ 32) :
    (some (BitVec.ofNat 32 (N - k) - 1 == 0) : Option Bool).map (!·) = some (decide (k + 1 < N)) := by
  rw [cnt_next hk, ofNat_beq_zero (by omega)]
  simp only [Option.map_some, Option.some.injEq]
  by_cases h : k + 1 < N
  · simp [h, show N - (k + 1) ≠ 0 by omega]
  · simp [h, show N - (k + 1) = 0 by omega]

/-! ## States -/

/-- `s'` is `s` but for the registers `ds` and the flags. -/
structure Only (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Only.refl (ds : List Reg) (s : State) : Only ds s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Only.trans {ds es : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only ds s₁ s₂) (h₂ : Only es s₂ s₃) :
    Only (ds ++ es) s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1], h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Only.mono {ds es : List Reg} {s s' : State} (h : Only ds s s') (he : ∀ r ∈ ds, r ∈ es) :
    Only es s s' := ⟨fun r hr => h.gpr r fun h' => hr (he r h'), h.mem, h.rd, h.wr⟩

/-! ## Single instructions -/

theorem wp_cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

/-- `mov d, [b + disp]` -/
theorem wp_movm {d b : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ b disp)) 4)
    (k : WP isa (.block is) (s.setReg d (s.mem.readW (s.ea (at_ b disp)) 32)) Q) :
    WP isa (.block (.mov d (.mem (at_ b disp)) :: is)) s Q :=
  wp_cons (by simp only [exec, readSrc, State.load32, hin, ite_true, Option.map_some]) k

/-- `movzx d, byte [b + disp]` -/
theorem wp_movzx {d b : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ b disp)) 1)
    (k : WP isa (.block is) (s.setReg d ((s.mem (s.ea (at_ b disp))).setWidth 32)) Q) :
    WP isa (.block (.movzx8 d (at_ b disp) :: is)) s Q :=
  wp_cons (by simp only [exec, State.load8, hin, ite_true, Option.map_some]) k

/-! ## Addresses -/

/-- `[x + k + d]` of a 32-bit pointer `x`, where nothing wraps around. -/
theorem addr_add {x : BitVec 32} {k d : Nat} (h : x.toNat + k + d < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 k) d = x.setWidth 64 + BitVec.ofNat 64 (k + d) := by
  simp only [addr]
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + k) (by omega), Nat.mod_eq_of_lt (a := x.toNat + k + d) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + k + d) (by omega), Nat.mod_eq_of_lt (a := x.toNat) (by omega),
    Nat.mod_eq_of_lt (a := k + d) (by omega), Nat.mod_eq_of_lt (a := x.toNat + (k + d)) (by omega)]
  omega

/-- The same, as the model computes it for an access `[r + d]` with `r = x + k`. -/
theorem ea_add {x : BitVec 32} {k d : Nat} (h : x.toNat + k + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 k + BitVec.ofNat 32 d).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 (k + d) :=
  addr_add h

/-- An access of `n` bytes at offset `o` of a region at a 32-bit pointer. -/
theorem contains_at {x : BitVec 32} {len o n : Nat} (h : o + n ≤ len) (hx : x.toNat + len ≤ 2 ^ 32) :
    (⟨x.setWidth 64, len⟩ : Region).Contains (x.setWidth 64 + BitVec.ofNat 64 o) n := by
  simp only [Region.Contains]
  rw [show x.setWidth 64 + BitVec.ofNat 64 o - x.setWidth 64 = BitVec.ofNat 64 o by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact h

/-- Coefficient `k` of a polynomial at a 32-bit pointer. -/
theorem coeffAddr_eq (x : BitVec 32) (k : Nat) :
    coeffAddr (x.setWidth 64) k = x.setWidth 64 + BitVec.ofNat 64 (4 * k) := rfl

/-- Two accesses at offsets `a` and `b` of a region at a 32-bit pointer. -/
theorem sep_at {x : BitVec 32} {len a b n k : Nat} (ha : a + n ≤ len) (hb : b + k ≤ len)
    (hx : x.toNat + len ≤ 2 ^ 32) (h : a + n ≤ b ∨ b + k ≤ a) :
    Mem.Sep (x.setWidth 64 + BitVec.ofNat 64 a) n (x.setWidth 64 + BitVec.ofNat 64 b) k := by
  intro y hy hy'
  have := x.isLt
  have hx' := toNat_setWidth64 x
  generalize x.setWidth 64 = X at *
  bv_omega

end VG.Proof.MlKem.X86
