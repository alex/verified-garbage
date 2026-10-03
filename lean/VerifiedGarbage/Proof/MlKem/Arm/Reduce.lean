import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Impl.MlKem.Arm.Ntt

/-!
# ML-KEM on 32-bit ARM: Barrett reduction, the tables and the saved registers

`reduce` computes `x mod q` of any `x < 2²⁵` (`red_toNat`), through
`barrett32` (`Proof/MlKem/Arith.lean`); `table` stores a table of 128 `u32`s
(`table_ok`), and the tables of the code are those of the standard
(`zetaTable_eq`, `gammaTable_eq`); `saveRegs` and `restoreRegs` keep our
caller's `r4`–`r11` in memory.
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem

/-! ## Barrett reduction -/

/-- What `barrett d t c` leaves in `d`, with `c` in `c`. -/
def bar (c x : BitVec 32) : BitVec 32 :=
  x - (x >>> 11 * c) >>> 18 - (x >>> 11 * c) >>> 18 <<< 8 - (x >>> 11 * c) >>> 18 <<< 10 -
    (x >>> 11 * c) >>> 18 <<< 11

/-- What `reduce d t c` leaves in `d`. -/
def red (c x : BitVec 32) : BitVec 32 := fixq (bar c x - 3328 - 1)

/-- The constant of `consts`. -/
def C : BitVec 32 := 161270

theorem consts_val : ((0x2 : BitVec 16) ++ ((0x75F6 : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = C := by
  decide

theorem bar_toNat {x : BitVec 32} (hx : x.toNat < 2 ^ 25) : (bar C x).toNat = barrett32 x.toNat := by
  obtain ⟨b1, b2⟩ := barrett32_bounds hx
  have hT : ((x >>> 11 * C) >>> 18).toNat = barrett32Quot x.toNat := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow, show C.toNat = 161270 from rfl, Nat.mod_eq_of_lt b1]
    rfl
  unfold bar barrett32
  generalize (x >>> 11 * C) >>> 18 = T at hT
  rw [q_eq] at b2 ⊢
  bv_omega

theorem red_toNat {x : BitVec 32} (hx : x.toNat < 2 ^ 25) : (red C x).toNat = x.toNat % q := by
  have h1 := barrett32_lt hx
  unfold red
  rw [fixq_subq (by rw [bar_toNat hx]; exact h1), bar_toNat hx, ← reduce32 hx, condSub_eq h1]

theorem red_lt {x : BitVec 32} (hx : x.toNat < 2 ^ 25) : (red C x).toNat < q := by
  rw [red_toNat hx]; exact Nat.mod_lt _ (by decide)

/-- A product of reduced values, reduced. -/
theorem red_mul {a b : Zq} :
    red C (BitVec.ofNat 32 a.val * BitVec.ofNat 32 b.val) = BitVec.ofNat 32 (a * b).val := by
  have ha := val_lt a
  have hb := val_lt b
  have hp : (BitVec.ofNat 32 a.val * BitVec.ofNat 32 b.val).toNat = a.val * b.val := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a.val) (by omega),
      Nat.mod_eq_of_lt (a := b.val) (by omega)]
    exact Nat.mod_eq_of_lt (by have := mul_lt_q2 ha hb; omega)
  refine ofNat_val_eq ?_
  rw [red_toNat (by rw [hp]; have := mul_lt_q2 ha hb; omega), hp, val_mul]

/-! ## Tables -/

theorem zetaTable_eq : zetaTable = zetas := rfl

theorem gammaTable_eq : gammaTable = gammas := rfl

theorem zetaTable_lt : ∀ k < 128, zetaTable.getD k 0 < q := by decide +kernel

theorem gammaTable_lt : ∀ k < 128, gammaTable.getD k 0 < q := by decide +kernel

/-- An entry of a table, as `movw` builds it. -/
theorem movw_val {v : Nat} (hv : v < 65536) : (BitVec.ofNat 16 v).setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt (by omega)]

/-- After the first `k` entries of a table at `b`. -/
structure TabInv (T : List Nat) (b : Reg) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr (s₀.gpr b), 512⟩] s₀.mem s.mem
  tab : ∀ j < k, s.mem.readW (State.addr (s₀.gpr b) + BitVec.ofNat 64 (4 * j)) 32 =
    BitVec.ofNat 32 (T.getD j 0)

theorem tab_step {s : State} {b : Reg} {B : BitVec 32} {k : Nat} (hk : 4 * k < 4096) (hb : s.gpr b = B)
    (hin : InRegions s.wr (State.addr (B + BitVec.ofNat 32 (4 * k))) 4) (v : BitVec 16) (hbr : b ≠ .r12) :
    WP isa (.block [.movw .r12 v, .str .r12 b (4 * k)]) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW (State.addr (B + BitVec.ofNat 32 (4 * k))) (v.setWidth 32) := by
  have ho : 4 * k < 4096 := hk
  run_block [hb, hbr, hin, ho, ite_false, implies_true]
  exact ⟨fun r hr => ite_eq_right hr, trivial⟩

/-- `table T b` stores the table `T` at `b`. -/
theorem table_ok (T : List Nat) (hT : ∀ k < 128, T.getD k 0 < 65536) {b : Reg} (hb : b ≠ .r12)
    {s₀ : State} (hfit : (s₀.gpr b).toNat + 512 ≤ 2 ^ 32)
    (hwr : ∀ k < 128, InRegions s₀.wr (State.addr (s₀.gpr b) + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (table T b)) s₀ (TabInv T b s₀ 128) := by
  refine wp_range_flatMap (M := isa) (TabInv T b s₀) (fun k s hk h => ?_) 128 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : State.addr (s₀.gpr b + BitVec.ofNat 32 (4 * k)) = State.addr (s₀.gpr b) + BitVec.ofNat 64 (4 * k) :=
    addr_add (by omega)
  refine WP.mono (tab_step (k := k) (by omega) (h.gpr b hb) (by rw [ea, h.wr]; exact hwr k hk) _ hb)
    fun s' ⟨g, rd, wr, sp, m⟩ => ⟨fun r hr => (g r hr).trans (h.gpr r hr), rd.trans h.rd, wr.trans h.wr,
      sp.trans h.sp, ?_, fun j hj => ?_⟩
  · rw [m, ea]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))
  · rw [m, ea, movw_val (hT k hk)]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)]
      exact h.tab j (by omega)

/-! ## Regions at offsets from a base -/

theorem region_sub_off {S : Addr} {o n len : Nat} (h : o + n ≤ len) :
    Region.Sub ⟨S + BitVec.ofNat 64 o, n⟩ ⟨S, len⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  bv_omega

theorem region_disj_off {S : Addr} {o₁ n₁ o₂ n₂ L : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁)
    (h₁ : o₁ + n₁ ≤ L) (h₂ : o₂ + n₂ ≤ L) (hS : S.toNat + L ≤ 2 ^ 64) :
    Region.Disjoint ⟨S + BitVec.ofNat 64 o₁, n₁⟩ ⟨S + BitVec.ofNat 64 o₂, n₂⟩ := by
  intro a ha hb
  simp only [Region.Contains] at ha hb
  bv_omega

theorem add_ofNat_zero (S : Addr) : S + BitVec.ofNat 64 0 = S := by simp

theorem add_ofNat_add (S : Addr) (a b : Nat) :
    S + BitVec.ofNat 64 a + BitVec.ofNat 64 b = S + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ptr_add_add32 (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem addr_toNat64 (a : BitVec 32) : (State.addr a).toNat + 2 ^ 32 ≤ 2 ^ 64 := by
  rw [addr_toNat]; have := a.isLt; omega

/-- A pointer to `L ≤ 2³²` bytes, as a 64-bit address, does not wrap around. -/
theorem addr_fit (a : BitVec 32) {L : Nat} (hL : L ≤ 2 ^ 32) : (State.addr a).toNat + L ≤ 2 ^ 64 :=
  Nat.le_trans (Nat.add_le_add_left hL _) (addr_toNat64 a)

theorem fit_le {a : BitVec 32} {k L : Nat} (hk : k ≤ L) (h : a.toNat + L ≤ 2 ^ 32) : a.toNat + k ≤ 2 ^ 32 :=
  Nat.le_trans (Nat.add_le_add_left hk _) h

/-! ## Saved registers -/

theorem savedRegs_nodup : ∀ i < 8, ∀ j < 8, savedRegs.getD i .r4 = savedRegs.getD j .r4 → i = j := by
  decide

theorem savedRegs_mem : ∀ i < 8, savedRegs.getD i .r4 ∈ savedRegs := by decide

theorem savedRegs_ne_lr : ∀ i < 8, savedRegs.getD i .r4 ≠ .lr := by decide

/-- The registers `g` saved at `A`. -/
def Saved (m : Mem) (A : Addr) (g : Reg → BitVec 32) : Prop :=
  ∀ i < 8, m.readW (A + BitVec.ofNat 64 (4 * i)) 32 = g (savedRegs.getD i .r4)

/-- After saving the first `k` registers at `A = b + off`. -/
structure SaveInv (b : Reg) (off : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr (s₀.gpr b) + BitVec.ofNat 64 off, 32⟩] s₀.mem s.mem
  saved : ∀ i < k, s.mem.readW (State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * i)) 32 =
    s₀.gpr (savedRegs.getD i .r4)

theorem saveRegs_ok (b : Reg) {off : Nat} (ho : off + 28 < 4096) {s₀ : State}
    (hfit : (s₀.gpr b).toNat + (off + 32) ≤ 2 ^ 32)
    (hwr : ∀ i < 8, InRegions s₀.wr (State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (saveRegs b off)) s₀ (SaveInv b off s₀ 8) := by
  refine wp_range_flatMap (M := isa) (SaveInv b off s₀) (fun k s hk h => ?_) 8 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : State.addr (s.gpr b + BitVec.ofNat 32 (off + 4 * k)) =
      State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * k) := by
    rw [h.gpr, addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_str (by omega) (by rw [ea, h.wr]; exact hwr k hk), runStep_some, runBlock_nil]
  refine ⟨_, rfl, h.gpr, h.rd, h.wr, h.sp, ?_, fun j hj => ?_⟩
  · rw [ea]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))
  · show (s.mem.writeW _ _).readW _ _ = _
    rw [ea, h.gpr]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)]
      exact h.saved j (by omega)

/-- After loading the first `k` registers from `A = b + off`. -/
structure RestoreInv (g : Reg → BitVec 32) (s₀ : State) (k : Nat) (s : State) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  other : ∀ r, r ∉ savedRegs → s.gpr r = s₀.gpr r
  loaded : ∀ i < k, s.gpr (savedRegs.getD i .r4) = g (savedRegs.getD i .r4)

theorem restoreRegs_ok (b : Reg) (hb : b ∉ savedRegs) {off : Nat} (ho : off + 28 < 4096) {s₀ : State}
    (hfit : (s₀.gpr b).toNat + (off + 32) ≤ 2 ^ 32) {g : Reg → BitVec 32}
    (hs : Saved s₀.mem (State.addr (s₀.gpr b) + BitVec.ofNat 64 off) g)
    (hrd : ∀ i < 8, InRegions (s₀.rd ++ s₀.wr)
      (State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (restoreRegs b off)) s₀ (RestoreInv g s₀ 8) := by
  refine wp_range_flatMap (M := isa) (RestoreInv g s₀) (fun k s hk h => ?_) 8 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : State.addr (s.gpr b + BitVec.ofNat 32 (off + 4 * k)) =
      State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * k) := by
    rw [h.other b hb, addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_ldr (by omega) (by rw [ea, h.rd, h.wr]; exact hrd k hk), runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, h.mem, h.rd, h.wr, h.sp, fun r hr => ?_, fun j hj => ?_⟩
  · show (s.setReg _ _).gpr r = _
    simp only [State.setReg]
    rw [ite_eq_right (fun (e : r = savedRegs.getD k .r4) => hr (e ▸ savedRegs_mem k hk)), h.other r hr]
  · show (s.setReg _ _).gpr _ = _
    simp only [State.setReg]
    by_cases e : j = k
    · subst e; rw [ite_eq_left rfl, ea, h.mem]; exact hs j hk
    · rw [ite_eq_right (fun e' => e (savedRegs_nodup j (by omega) k hk e'))]
      exact h.loaded j (by omega)

/-- The callee-saved registers, restored. -/
theorem preserved_of_restore {g : Reg → BitVec 32} {s₀ s : State} (h : RestoreInv g s₀ 8 s)
    (hlr : s₀.gpr .lr = g .lr) : ∀ r ∈ preserved, s.gpr r = g r := by
  have : ∀ r ∈ preserved, r = .lr ∨ ∃ i < 8, savedRegs.getD i .r4 = r := by decide
  intro r hr
  rcases this r hr with rfl | ⟨i, hi, rfl⟩
  · rw [h.other .lr (by decide), hlr]
  · exact h.loaded i hi

end VG.Proof.MlKem.Arm
