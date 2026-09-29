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

theorem sub_beq_zero (x v : BitVec 32) : (x - v == 0) = decide (x.toNat = v.toNat) := by
  by_cases h : x.toNat = v.toNat
  · have e : x = v := BitVec.eq_of_toNat_eq h
    subst e; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    exact h (by have := congrArg BitVec.toNat e; simp only [BitVec.toNat_sub] at this; bv_omega)

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

/-! ## Bits -/

/-- A value less than `2ⁿ`, rotated right by `n`, is shifted left by `32 - n`. -/
theorem rotr_small (x : BitVec 32) {n : Nat} (h0 : 0 < n) (h : n < 32) (hx : x.toNat < 2 ^ n) :
    (x.rotateRight n).toNat = x.toNat * 2 ^ (32 - n) := by
  rw [BitVec.rotateRight_def, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  simp only [Nat.mod_eq_of_lt h]
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hx, Nat.zero_or, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have : x.toNat * 2 ^ (32 - n) < 2 ^ n * 2 ^ (32 - n) := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
  rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)] at this
  exact this

theorem toNat_shr (x : BitVec 32) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_and_mask (x : BitVec 32) (k : Nat) (hk : k < 32) :
    (x &&& BitVec.ofNat 32 (2 ^ k - 1)).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    have : 2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
    omega), Nat.and_two_pow_sub_one_eq_mod]

/-- The low byte of a word. -/
theorem setWidth8_eq (x : BitVec 32) : x.setWidth 8 = BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- A byte, zero-extended. -/
theorem toNat_byte32 (b : Byte) : (b.setWidth 32).toNat = b.toNat := by
  simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := b.isLt; omega)

/-- `csub` as the code computes it, as a word. -/
theorem csub_eq (x d : BitVec 32) (hx : x.toNat < 2 * q) :
    x - Q + ((d - d - (BitVec.ofBool (decide (x.toNat < Q.toNat))).setWidth 32) &&& Q) =
      BitVec.ofNat 32 (x.toNat % q) := by
  apply BitVec.eq_of_toNat_eq
  rw [condSub_bv x d hx, condSub_eq hx, toNat_ofNat32 (by rw [q_eq]; omega)]

/-- Coefficients `i < k + c` after `c` words `V (k + t)` are written. -/
theorem coef_extend2 {m : Mem} {p : Addr} {V : Nat → BitVec 32} {k : Nat} (hk : k + 2 ≤ 256)
    (h : ∀ i < k, coeffAt m p i = V i) :
    ∀ i < k + 2, coeffAt ((m.writeW (coeffAddr p k) (V k)).writeW (coeffAddr p (k + 1)) (V (k + 1))) p i =
      V i := by
  intro i hi
  rw [coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) (show k + 1 < n by rw [n_eq]; omega),
    coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) (show k < n by rw [n_eq]; omega)]
  by_cases e1 : k + 1 = i
  · rw [ite_eq_left e1, e1]
  rw [ite_eq_right e1]
  by_cases e0 : k = i
  · rw [ite_eq_left e0, e0]
  rw [ite_eq_right e0]
  exact h i (by omega)

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

/-- `mov d, r` -/
theorem wp_movr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : WP isa (.block is) (s.setReg d (s.gpr r)) Q) : WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  wp_cons (by simp only [exec, readSrc, Option.map_some]) k

/-- `mov [b + disp], r` -/
theorem wp_store {b r : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions s.wr (s.ea (at_ b disp)) 4)
    (k : WP isa (.block is) { s with mem := s.mem.writeW (s.ea (at_ b disp)) (s.gpr r) } Q) :
    WP isa (.block (.store (at_ b disp) r :: is)) s Q :=
  wp_cons (by simp only [exec, State.store32, hin, ite_true]) k

/-- `shr d, n` -/
theorem wp_shr {d : Reg} {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) {is : List Instr} {s : State}
    {Q : State → Prop} (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d >>> n → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  refine wp_cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some (s.gpr d >>> n == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_)
  · simp only [exec, execShift, h1, h2, and_self, ite_true]
  · simp only [State.setReg]
    rw [ite_eq_right_iff.mpr fun (e : r = d) => absurd (e ▸ List.mem_singleton_self d) hr]
    rfl
  · simp [State.setReg]

theorem Only.setReg (s : State) (r : Reg) (v : BitVec 32) : Only [r] s (s.setReg r v) :=
  ⟨fun x hx => by
    simp only [State.setReg]
    rw [ite_eq_right_iff.mpr fun (e : x = r) => absurd (e ▸ List.mem_singleton_self r) hx], rfl, rfl, rfl⟩

/-- `and r, imm` -/
theorem wp_and {r : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [r] s s' → s'.gpr r = s.gpr r &&& v → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and r (.imm v) :: is)) s Q := by
  refine wp_cons (s' := (arithFlags s (s.gpr r &&& v) false false).setReg r (s.gpr r &&& v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some]) (k _ ⟨fun x hx => ?_, rfl, rfl, rfl⟩ ?_)
  · simp only [State.setReg]
    rw [ite_eq_right_iff.mpr fun (e : x = r) => absurd (e ▸ List.mem_singleton_self r) hx]
    rfl
  · simp [State.setReg]

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

theorem polyLen (p : Addr) : (polyRegion p).len ≤ 2 ^ 64 := by show 1024 ≤ 2 ^ 64; decide

/-- Offsets within a region that does not wrap are distinct addresses. -/
theorem add_ofNat_ne {x : Addr} {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    x + BitVec.ofNat 64 a ≠ x + BitVec.ofNat 64 b := by
  intro e
  have e' : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
    have := congrArg (fun y => y - x) e; simpa using this
  have := congrArg BitVec.toNat e'
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact h this

/-- Bytes `j < k + c` at `o`, after `c` bytes `x t` are written at `o + k + t` to bytes `j < k` of
`L`. -/
theorem bytes_extend {m : Mem} {o : Addr} {L : List Byte} {k : Nat} (hk : k + 3 < 2 ^ 64)
    (h : ∀ j < k, m (o + BitVec.ofNat 64 j) = L[j]!) {x0 x1 x2 : Byte} (h0 : x0 = L[k]!)
    (h1 : x1 = L[k + 1]!) (h2 : x2 = L[k + 2]!) :
    ∀ j < k + 3, ((m.writeW (o + BitVec.ofNat 64 k) x0).writeW (o + BitVec.ofNat 64 (k + 1)) x1).writeW
      (o + BitVec.ofNat 64 (k + 2)) x2 (o + BitVec.ofNat 64 j) = L[j]! := by
  intro j hj
  simp only [writeW8_apply]
  by_cases e2 : j = k + 2
  · subst e2; simp [h2]
  rw [ite_eq_right_iff.mpr fun e => absurd e (add_ofNat_ne (by omega) (by omega) e2)]
  by_cases e1 : j = k + 1
  · subst e1; simp [h1]
  rw [ite_eq_right_iff.mpr fun e => absurd e (add_ofNat_ne (by omega) (by omega) e1)]
  by_cases e0 : j = k
  · subst e0; simp [h0]
  rw [ite_eq_right_iff.mpr fun e => absurd e (add_ofNat_ne (by omega) (by omega) e0)]
  exact h j (by omega)

/-- Bytes `j < k + 1` at `o`, after the byte `x = L[k]` is written at `o + k`. -/
theorem bytes_extend1 {m : Mem} {o : Addr} {L : List Byte} {k : Nat} (hk : k < 2 ^ 64)
    (h : ∀ j < k, m (o + BitVec.ofNat 64 j) = L[j]!) {x : Byte} (hx : x = L[k]!) :
    ∀ j < k + 1, (m.writeW (o + BitVec.ofNat 64 k) x) (o + BitVec.ofNat 64 j) = L[j]! := by
  intro j hj
  simp only [writeW8_apply]
  by_cases e : j = k
  · subst e; simp [hx]
  rw [ite_eq_right_iff.mpr fun e' => absurd e' (add_ofNat_ne (by omega) (by omega) e)]
  exact h j (by omega)

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

/-- All-zero memory holds a reduced polynomial. -/
theorem reduced_of_zero {m : Mem} {p : Addr} (h : ∀ k < 1024, m (p + BitVec.ofNat 64 k) = 0) :
    VG.Spec.MlKem.Reduced m p := fun i hi => by
  rw [VG.Proof.MlKem.coeffAt_congr (m' := m) (m := fun _ => 0) (fun k hk => h k hk) hi]
  simp [VG.Spec.MlKem.coeffAt, Mem.readW, Mem.read]

/-- Memory that is zero but at the arguments above `0x5004`, which hold
`ws`: polynomials below `0x5000` are all zero. -/
theorem reduced_below {m : Mem} (hm : ∀ a : Addr, a.toNat < 0x5000 → m a = 0) (p : Nat)
    (hp : p + 1024 ≤ 0x5000) : VG.Spec.MlKem.Reduced m (BitVec.ofNat 64 p) :=
  reduced_of_zero fun k hk => hm _ (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
end VG.Proof.MlKem.X86
