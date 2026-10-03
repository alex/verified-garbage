import VerifiedGarbage.Proof.X25519.AArch64.Arith
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.X25519.AArch64

/-!
# X25519 on AArch64: the steps of the field operations

The field operations read and write words of the working space (`x3`, 4096
bytes) at constant offsets; each lemma here runs a few instructions and states
their effect on the numbers in the registers and in the words of the working
space.
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64

/-- The value of a register, as a number. -/
abbrev v (s : State) (r : Reg) : Nat := (s.gpr r).toNat

/-- The 64-bit word at `b + off`, as a number. -/
def wd (m : Mem) (b : Addr) (off : Nat) : Nat := (m.readW (b + BitVec.ofNat 64 off) 64).toNat

/-- The working space at `b`. -/
abbrev scR (b : Addr) : Region := ⟨b, 4096⟩

/-- The working space is at `b`, in `x3`, and writable. -/
structure Sc (b : Addr) (s : State) : Prop where
  x3 : s.gpr .x3 = b
  wr : scR b ∈ s.wr

/-- The registers but `W` are unchanged, and so are the regions. -/
structure Kp (W : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ W → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Kp.refl (W : List Reg) (s : State) : Kp W s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Kp.trans {W W' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Kp W s₁ s₂) (h₂ : Kp W' s₂ s₃) :
    Kp (W ++ W') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1], h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Kp.mono {W W' : List Reg} {s s' : State} (h : Kp W s s') (hs : ∀ r ∈ W, r ∈ W') :
    Kp W' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr⟩

theorem Kp.sub {W W' : List Reg} {s s' : State} (h : Kp W s s') (hs : W ⊆ W') : Kp W' s s' :=
  h.mono fun _ hr => hs hr

/-- Closes `W ⊆ W'` for lists of registers, some of them variables. -/
macro "sub_regs" : tactic => `(tactic| simp only [List.cons_subset, List.append_subset, List.nil_subset,
  List.mem_cons, List.mem_append, true_or, or_true, and_true, List.not_mem_nil, or_false, and_self,
  List.cons_append, List.nil_append])

theorem Sc.of_kp {b : Addr} {W : List Reg} {s s' : State} (hs : Sc b s) (h : Kp W s s')
    (hW : Reg.x3 ∉ W) : Sc b s' :=
  ⟨by rw [h.gpr _ hW, hs.x3], by rw [h.wr]; exact hs.wr⟩

theorem Sc.mem {b : Addr} {s : State} (hs : Sc b s) (m : Mem) : Sc b { s with mem := m } :=
  ⟨hs.x3, hs.wr⟩

/-- An offset of a word in the working space. -/
def Off (off : Nat) : Prop := off % 8 = 0 ∧ off + 8 ≤ 4096

instance (off : Nat) : Decidable (Off off) := by unfold Off; infer_instance

/-! ## Registers after writes -/

section
variable (s : State)

theorem read_x (r : Reg) : s.read .x r = s.gpr r := by
  simp only [State.read, BitVec.setWidth_eq]

theorem gpr_wx (d : Reg) (x : BitVec 64) (r : Reg) :
    (s.write .x d x).gpr r = if r = d then x else s.gpr r := by
  simp only [State.write, BitVec.setWidth_eq]

theorem gpr_wx_self (d : Reg) (x : BitVec 64) : (s.write .x d x).gpr d = x := by
  simp only [gpr_wx, ite_true]

theorem gpr_wx_ne {d r : Reg} (x : BitVec 64) (h : r ≠ d) : (s.write .x d x).gpr r = s.gpr r := by
  simp only [gpr_wx, h, ite_false]

theorem gpr_ww_self (d : Reg) (x : BitVec 32) : (s.write .w d x).gpr d = x.setWidth 64 := by
  simp only [State.write, ite_true]

theorem gpr_ww_ne {d r : Reg} (x : BitVec 32) (h : r ≠ d) : (s.write .w d x).gpr r = s.gpr r := by
  simp only [State.write, h, ite_false]

theorem mem_ww (d : Reg) (x : BitVec 32) : (s.write .w d x).mem = s.mem := rfl

theorem kp_ww (d : Reg) (x : BitVec 32) : Kp [d] s (s.write .w d x) :=
  ⟨fun r hr => gpr_ww_ne s x (by simpa using hr), rfl, rfl⟩

theorem sc_ww {b : Addr} {d : Reg} (x : BitVec 32) (hs : Sc b s) (hd : d ≠ .x3) :
    Sc b (s.write .w d x) :=
  ⟨by rw [gpr_ww_ne s x (Ne.symm hd), hs.x3], hs.wr⟩

theorem mem_wx (d : Reg) (x : BitVec 64) : (s.write .x d x).mem = s.mem := rfl
theorem rd_wx (d : Reg) (x : BitVec 64) : (s.write .x d x).rd = s.rd := rfl
theorem wr_wx (d : Reg) (x : BitVec 64) : (s.write .x d x).wr = s.wr := rfl

theorem kp_wx (d : Reg) (x : BitVec 64) : Kp [d] s (s.write .x d x) :=
  ⟨fun r hr => gpr_wx_ne s x (by simpa using hr), rfl, rfl⟩

theorem sc_wx {b : Addr} {d : Reg} (x : BitVec 64) (hs : Sc b s) (hd : d ≠ .x3) :
    Sc b (s.write .x d x) :=
  ⟨by rw [gpr_wx_ne s x (Ne.symm hd), hs.x3], hs.wr⟩

end

/-! ## Instructions -/

theorem off_in {b : Addr} {s : State} (hs : Sc b s) {off : Nat} (ho : Off off) :
    InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 off) 8 :=
  ⟨scR b, hs.wr, by rw [hs.x3]; exact Offset.contains_base b ho.2 (by have := ho.2; omega)⟩

theorem exec_ld {b : Addr} {s : State} (hs : Sc b s) (t : Reg) {off : Nat} (ho : Off off) :
    exec (ld t off) s = some (s.write .x t (s.mem.readW (b + BitVec.ofNat 64 off) 64)) := by
  have h := off_in hs ho
  rw [ld, exec_ldr_x ⟨ho.1, by have := ho.2; omega⟩ (by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩), hs.x3]

theorem exec_st {b : Addr} {s : State} (hs : Sc b s) (t : Reg) {off : Nat} (ho : Off off) :
    exec (st t off) s = some { s with mem := s.mem.writeW (b + BitVec.ofNat 64 off) (s.gpr t) } := by
  rw [st, exec_str_x ⟨ho.1, by have := ho.2; omega⟩ (off_in hs ho), hs.x3]

theorem exec_madd_x {s : State} {d n m a : Reg} :
    exec (.madd .x d n m a) s = some (s.write .x d (s.gpr a + s.gpr n * s.gpr m)) := by
  simp only [exec, read_x]

theorem exec_mul_x {s : State} {d n m : Reg} :
    exec (.mul .x d n m) s = some (s.write .x d (s.gpr n * s.gpr m)) := by
  simp only [exec, read_x]

theorem exec_add_x {s : State} {d n m : Reg} :
    exec (.add .x d n m) s = some (s.write .x d (s.gpr n + s.gpr m)) := by
  simp only [exec, read_x]

theorem exec_sub_x {s : State} {d n m : Reg} :
    exec (.sub .x d n m) s = some (s.write .x d (s.gpr n - s.gpr m)) := by
  simp only [exec, read_x]

theorem exec_and_x {s : State} {d n m : Reg} :
    exec (.logic .and .x d n m) s = some (s.write .x d (s.gpr n &&& s.gpr m)) := by
  simp only [exec, read_x]

theorem exec_eor_x {s : State} {d n m : Reg} :
    exec (.logic .eor .x d n m) s = some (s.write .x d (s.gpr n ^^^ s.gpr m)) := by
  simp only [exec, read_x]

theorem exec_lsr {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsr .x d n sh) s = some (s.write .x d (s.gpr n >>> sh)) := by
  simp only [exec, Size.bits, h, ite_true, read_x]

theorem exec_lsl {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsl .x d n sh) s = some (s.write .x d (s.gpr n <<< sh)) := by
  simp only [exec, Size.bits, h, ite_true, read_x]

theorem exec_movz {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64)) := by
  simp only [exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true,
    BitVec.shiftLeft_zero]

theorem exec_movk1 {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.movk .x d imm 1) s = some (s.write .x d
      ((s.gpr d &&& ~~~((0xFFFF : BitVec 64) <<< 16)) ||| (imm.setWidth 64 <<< 16))) := by
  simp only [exec, Size.bits, Nat.mul_one, show (16 : Nat) < 64 from by decide, ite_true, read_x]

theorem exec_ldrb {s : State} {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.ldrb t n off) s = some (s.write .w t ((s.mem.read (s.gpr n + BitVec.ofNat 64 off) 1).setWidth 32)) := by
  simp only [exec, addr, Nat.mod_one, ho, true_and, ite_true, Option.bind_some,
    State.load, h, Option.map_some]

theorem exec_strb {s : State} {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.strb t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 1 ((s.read .w t).setWidth 8) } := by
  simp only [exec, addr, Nat.mod_one, show off < 4096 * 1 by omega, true_and, ite_true, Option.bind_some,
    State.store, h]

theorem read1_toNat (m : Mem) (a : Addr) : ((m.read a 1).setWidth 32).setWidth 64 = (m a).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, Mem.read, BitVec.toNat_append, show (0#0).toNat = 0 from rfl,
    Nat.zero_shiftLeft, Nat.zero_or]
  have := (m a).isLt
  omega

/-! ## Numbers -/

theorem madd_toNat (a b c : BitVec 64) :
    (a + b * c).toNat = (a.toNat + b.toNat * c.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod_mod]

theorem lsr_toNat (a : BitVec 64) (n : Nat) : (a >>> n).toNat = a.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem lsl_toNat (a : BitVec 64) (n : Nat) : (a <<< n).toNat = a.toNat * 2 ^ n % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem and_mask17 (a b : BitVec 64) (hb : b = 0x1ffff) : (a &&& b).toNat = a.toNat % 2 ^ 17 := by
  rw [hb, BitVec.toNat_and, show (0x1ffff : BitVec 64).toNat = 2 ^ 17 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem wd_def (m : Mem) (b : Addr) (off : Nat) :
    (m.readW (b + BitVec.ofNat 64 off) 64).toNat = wd m b off := rfl

/-! ## Multiply-accumulate -/

theorem not_mem3 {a b c d : Reg} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) : a ∉ [b, c, d] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2, h3⟩

theorem mac_ok {b : Addr} {s : State} (hs : Sc b s) {d : Reg} {oa ob : Nat} (hd17 : d ≠ .x17)
    (hd19 : d ≠ .x19) (hoa : Off oa) (hob : Off ob) :
    WP isa (.block (mac d oa ob)) s fun s' =>
      v s' d = (v s d + wd s.mem b oa * wd s.mem b ob) % 2 ^ 64 ∧ Kp [.x17, .x19, d] s s' ∧
        s'.mem = s.mem := by
  apply WP.of_runBlock
  have hs1 := sc_wx s (s.mem.readW (b + BitVec.ofNat 64 oa) 64) hs (show Reg.x17 ≠ .x3 by decide)
  simp only [mac, runBlock_cons, exec_ld hs _ hoa, runStep_some, exec_ld hs1 _ hob, mem_wx,
    exec_madd_x, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
  · simp only [v, gpr_wx_self, madd_toNat, gpr_wx_ne _ _ hd19, gpr_wx_ne _ _ hd17,
      gpr_wx_ne _ _ (show Reg.x17 ≠ .x19 by decide), wd_def]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_wx_ne _ _ hr.2.2, gpr_wx_ne _ _ hr.2.1, gpr_wx_ne _ _ hr.1]

/-- A chain of `mac`s. -/
theorem macs_ok {b : Addr} {d : Reg} (hd17 : d ≠ .x17) (hd19 : d ≠ .x19) (hd3 : d ≠ .x3) :
    ∀ (L : List (Nat × Nat)) (s : State), Sc b s → (∀ p ∈ L, Off p.1 ∧ Off p.2) →
    WP isa (.block (macs d L)) s fun s' =>
      v s' d = (v s d + (L.map fun p => wd s.mem b p.1 * wd s.mem b p.2).sum) % 2 ^ 64 ∧
        Kp [.x17, .x19, d] s s' ∧ s'.mem = s.mem
  | [], s, _, _ => by
    refine WP.block_nil ⟨?_, Kp.refl _ _, rfl⟩
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    exact (Nat.mod_eq_of_lt (s.gpr d).isLt).symm
  | p :: L, s, hs, hL => by
    obtain ⟨h1, h2⟩ := hL p List.mem_cons_self
    rw [macs, List.flatMap_cons]
    refine WP.block_append (WP.mono (mac_ok hs hd17 hd19 h1 h2) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (not_mem3 (by decide) (by decide) (Ne.symm hd3))
    refine WP.mono (macs_ok hd17 hd19 hd3 L s₁ hs₁ fun q hq => hL q (List.mem_cons_of_mem _ hq))
      fun s₂ ⟨e₂, k₂, m₂⟩ => ⟨?_, (k₁.trans k₂).mono fun r hr => ?_, m₂.trans m₁⟩
    · rw [e₂, m₁, e₁, List.map_cons, List.sum_cons, Nat.mod_add_mod, Nat.add_assoc]
    · exact (List.mem_append.mp hr).elim id id

/-- A sum over `List.range` as `sumR`. -/
theorem sum_range_list (t : Nat → Nat) (n : Nat) :
    ((List.range n).map t).sum = sumR t n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sumR]; simp

/-- The limbs of the element at `b + o`. -/
def limbs (m : Mem) (b : Addr) (o : Nat) (i : Nat) : Nat := if i < 15 then wd m b (o + 8 * i) else 0

/-- An element's offset: its fifteen words are in the working space. -/
def Slot (o : Nat) : Prop := o % 8 = 0 ∧ o + 120 ≤ 4096

instance (o : Nat) : Decidable (Slot o) := by unfold Slot; infer_instance

theorem Slot.off {o : Nat} (h : Slot o) {i : Nat} (hi : i < 15) : Off (o + 8 * i) :=
  ⟨by have := h.1; omega, by have := h.2; omega⟩

theorem dreg_facts : ∀ k < 15, dreg k ≠ .x17 ∧ dreg k ≠ .x19 ∧ dreg k ≠ .x20 ∧ dreg k ≠ .x21 ∧
    dreg k ≠ .x22 ∧ dreg k ≠ .x3 ∧ dreg k ≠ .x0 ∧ dreg k ≠ .x23 ∧ dreg k ≠ .x24 := by decide

theorem dreg_inj : ∀ j < 15, ∀ k < 15, dreg j = dreg k → j = k := by decide

theorem dreg_mem : ∀ k < 15, dreg k ∈ DR := by decide

/-- Column `k` of the product of the elements at `a` and `c`. -/
theorem col_ok {b : Addr} {s : State} (hs : Sc b s) (h19 : s.gpr .x21 = 19) {a c k : Nat}
    (ha : Slot a) (hc : Slot c) (hk : k < 15) :
    WP isa (.block (col a c k)) s fun s' =>
      v s' (dreg k) = colM (limbs s.mem b a) (limbs s.mem b c) k ∧
        Kp [.x17, .x19, .x20, dreg k] s s' ∧ s'.mem = s.mem := by
  obtain ⟨d17, d19, d20, d21, -, d3, -⟩ := dreg_facts k hk
  have hlo : ∀ p ∈ loPairs a c k, Off p.1 ∧ Off p.2 := fun p hp => by
    simp only [loPairs, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact ⟨ha.off (by omega), hc.off (by omega)⟩
  have hhi : ∀ p ∈ hiPairs a c k, Off p.1 ∧ Off p.2 := fun p hp => by
    simp only [hiPairs, List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    exact ⟨ha.off (by omega), hc.off (by omega)⟩
  rw [col]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_cons_iff.mpr ⟨_, exec_movz, ?_⟩
  have hs₀ := sc_wx s ((0 : BitVec 16).setWidth 64) hs d3
  refine WP.block_append (WP.mono (macs_ok d17 d19 d3 _ _ hs₀ hlo) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  have hs₁ := hs₀.of_kp k₁ (not_mem3 (by decide) (by decide) (Ne.symm d3))
  refine WP.block_cons_iff.mpr ⟨_, exec_movz, ?_⟩
  have hs₂ := sc_wx s₁ ((0 : BitVec 16).setWidth 64) hs₁ (show Reg.x20 ≠ .x3 by decide)
  refine WP.block_append (WP.mono (macs_ok (d := .x20) (by decide) (by decide) (by decide) _ _ hs₂ hhi)
    fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  refine WP.block_cons_iff.mpr ⟨_, exec_madd_x, WP.block_nil ⟨?_, ?_, ?_⟩⟩
  · have g1 : s₃.gpr (dreg k) = s₁.gpr (dreg k) := by
      rw [k₃.gpr _ (not_mem3 d17 d19 d20), gpr_wx_ne _ _ d20]
    have g2 : s₃.gpr .x21 = 19 := by
      rw [k₃.gpr _ (by decide), gpr_wx_ne _ _ (by decide),
        k₁.gpr _ (not_mem3 (by decide) (by decide) (Ne.symm d21)), gpr_wx_ne _ _ (Ne.symm d21), h19]
    have M1 : s₁.mem = s.mem := by rw [m₁, mem_wx]
    simp only [v, gpr_wx_self, madd_toNat, g1, g2]
    simp only [v, gpr_wx_self, mem_wx, M1] at e₁ e₃
    rw [e₃, e₁, colM, lo, hi, loPairs, hiPairs, List.map_map, List.map_map]
    simp only [BitVec.toNat_setWidth, Function.comp_def, sum_range_list,
      show (19 : BitVec 64).toNat = 19 from rfl]
    have hl : ∀ i < k + 1, wd s.mem b (a + 8 * i) * wd s.mem b (c + 8 * (k - i)) =
        limbs s.mem b a i * limbs s.mem b c (k - i) := fun i hi => by
      simp only [limbs, show i < 15 by omega, show k - i < 15 by omega, ite_true]
    have hh : ∀ j < 14 - k, wd s.mem b (a + 8 * (k + 1 + j)) * wd s.mem b (c + 8 * (14 - j)) =
        limbs s.mem b a (k + 1 + j) * limbs s.mem b c (14 - j) := fun j hj => by
      simp only [limbs, show k + 1 + j < 15 by omega, show 14 - j < 15 by omega, ite_true]
    rw [sumR_congr hl, sumR_congr hh, show (0 : BitVec 16).toNat = 0 from rfl,
      Nat.zero_mod, Nat.zero_add, Nat.zero_add]
  · exact (((kp_wx s _ _).trans k₁).trans (((kp_wx s₁ _ _).trans k₃).trans (kp_wx s₃ _ _))).sub
      (by sub_regs)
  · rw [mem_wx, m₃, mem_wx, m₁, mem_wx]

/-- The limb registers, as a function (zero beyond the fifteenth). -/
def regs (s : State) (k : Nat) : Nat := if k < 15 then v s (dreg k) else 0

/-- The registers the columns write. -/
abbrev colRegs : List Reg := DR ++ [.x17, .x19, .x20]

theorem dreg_sub {k : Nat} (hk : k < 15) : [Reg.x17, .x19, .x20, dreg k] ⊆ colRegs := by
  have := dreg_mem k hk
  simp only [List.cons_subset, List.nil_subset, and_true, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, true_or, or_true, this]

/-- The first `n` columns. -/
theorem cols_ok {b : Addr} {a c : Nat} (ha : Slot a) (hc : Slot c) :
    ∀ n ≤ 15, ∀ s : State, Sc b s → s.gpr .x21 = 19 →
    WP isa (.block ((List.range n).flatMap (col a c))) s fun s' =>
      (∀ k < n, v s' (dreg k) = colM (limbs s.mem b a) (limbs s.mem b c) k) ∧ Kp colRegs s s' ∧
        s'.mem = s.mem
  | 0, _, s, _, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Kp.refl _ _, rfl⟩
  | n + 1, hn, s, hs, h19 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (cols_ok ha hc n (by omega) s hs h19) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (by decide)
    have h19₁ : s₁.gpr .x21 = 19 := by rw [k₁.gpr _ (by decide), h19]
    refine WP.mono (col_ok hs₁ h19₁ ha hc (k := n) (by omega)) fun s₂ ⟨e₂, k₂, m₂⟩ =>
      ⟨fun k hk => ?_, (k₁.trans (k₂.sub (dreg_sub (by omega)))).sub
        (List.append_subset.mpr ⟨List.Subset.refl _, List.Subset.refl _⟩), m₂.trans m₁⟩
    · rw [m₁] at e₂
      by_cases hkn : k = n
      · rw [hkn, e₂]
      · obtain ⟨d17, d19, d20, -⟩ := dreg_facts k (by omega)
        have hne : dreg k ≠ dreg n := fun h => hkn (dreg_inj k (by omega) n (by omega) h)
        have hnot : dreg k ∉ [Reg.x17, .x19, .x20, dreg n] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨d17, d19, d20, hne⟩
        rw [v, k₂.gpr _ hnot]
        exact e₁ k (by omega)

/-! ## Carries -/

theorem dreg_ne {j k : Nat} (hj : j < 15) (hk : k < 15) (h : j ≠ k) : dreg j ≠ dreg k :=
  fun e => h (dreg_inj j hj k hk e)

/-- The carry out of limb `k` into limb `k'`. -/
theorem carryStep_ok {s : State} {k k' : Nat} (hk : k < 15) (hk' : k' < 15) (hkk : k ≠ k')
    (hm : s.gpr .x22 = 0x1ffff) :
    WP isa (.block (carryStep k k')) s fun s' =>
      regs s' = cstep k k' (regs s) ∧ Kp colRegs s s' ∧ s'.mem = s.mem := by
  obtain ⟨d17, -, -, -, d22, -⟩ := dreg_facts k hk
  obtain ⟨d17', -⟩ := dreg_facts k' hk'
  have hne := dreg_ne hk hk' hkk
  apply WP.of_runBlock
  simp only [carryStep, runBlock_cons, exec_lsr (show 17 < 64 by decide), runStep_some, exec_and_x,
    exec_add_x, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨funext fun i => ?_, ?_, rfl⟩
  · simp only [regs, cstep]
    by_cases hi : i < 15
    · simp only [hi, ite_true, show k < 15 from hk, show k' < 15 from hk']
      by_cases hik : i = k
      · subst hik
        rw [ite_eq_left rfl, v, gpr_wx_ne _ _ hne, gpr_wx_self, gpr_wx_ne _ _ d17, gpr_wx_ne _ _ (by decide),
          and_mask17 _ _ hm]
      · rw [ite_eq_right hik]
        by_cases hik' : i = k'
        · subst hik'
          rw [ite_eq_left rfl, v, gpr_wx_self, gpr_wx_ne _ _ (Ne.symm hne), gpr_wx_ne _ _ d17',
            gpr_wx_ne _ _ (Ne.symm d17), gpr_wx_self, BitVec.toNat_add, lsr_toNat]
        · rw [ite_eq_right hik']
          have h1 := dreg_ne hi hk hik
          have h2 := dreg_ne hi hk' hik'
          obtain ⟨e17, -⟩ := dreg_facts i hi
          rw [v, v, gpr_wx_ne _ _ h2, gpr_wx_ne _ _ h1, gpr_wx_ne _ _ e17]
    · simp only [hi, ite_false, show i ≠ k by omega, show i ≠ k' by omega]
  · exact (((kp_wx s _ _).trans (kp_wx _ _ _)).trans (kp_wx _ _ _)).sub (by
      have := dreg_mem k hk
      have := dreg_mem k' hk'
      simp only [List.cons_subset, List.nil_subset, and_true, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, true_or, or_true, *, List.cons_append, List.nil_append])

/-- The carry out of limb 14 into limb 0. -/
theorem foldTop_ok {s : State} (hm : s.gpr .x22 = 0x1ffff) (h19 : s.gpr .x21 = 19) :
    WP isa (.block foldTop) s fun s' =>
      regs s' = cfold (regs s) ∧ Kp colRegs s s' ∧ s'.mem = s.mem := by
  obtain ⟨d17, -, -, d21, d22, -⟩ := dreg_facts 14 (by decide)
  obtain ⟨e17, -, -, e21, e22, -⟩ := dreg_facts 0 (by decide)
  have hne := dreg_ne (j := 0) (k := 14) (by decide) (by decide) (by decide)
  apply WP.of_runBlock
  simp only [foldTop, runBlock_cons, exec_lsr (show 17 < 64 by decide), runStep_some, exec_and_x,
    exec_madd_x, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨funext fun i => ?_, ?_, rfl⟩
  · simp only [regs, cfold]
    by_cases hi : i < 15
    · simp only [hi, ite_true, show (14 : Nat) < 15 by decide, show (0 : Nat) < 15 by decide]
      by_cases hi14 : i = 14
      · subst hi14
        rw [ite_eq_left rfl, v, gpr_wx_ne _ _ (Ne.symm hne), gpr_wx_self, gpr_wx_ne _ _ d17,
          gpr_wx_ne _ _ (by decide), and_mask17 _ _ hm]
      · rw [ite_eq_right hi14]
        by_cases hi0 : i = 0
        · subst hi0
          rw [ite_eq_left rfl, v, gpr_wx_self, gpr_wx_ne _ _ hne, gpr_wx_ne _ _ e17,
            gpr_wx_ne _ _ (Ne.symm d17), gpr_wx_self, gpr_wx_ne _ _ (Ne.symm d21), gpr_wx_ne _ _ (by decide),
            h19, madd_toNat, lsr_toNat]
          rfl
        · rw [ite_eq_right hi0]
          have h1 := dreg_ne hi (by decide : (14 : Nat) < 15) hi14
          have h2 := dreg_ne hi (by decide : (0 : Nat) < 15) hi0
          obtain ⟨f17, -⟩ := dreg_facts i hi
          rw [v, v, gpr_wx_ne _ _ h2, gpr_wx_ne _ _ h1, gpr_wx_ne _ _ f17]
    · simp only [hi, ite_false, show i ≠ 14 by omega, show i ≠ 0 by omega]
  · exact (((kp_wx s _ _).trans (kp_wx _ _ _)).trans (kp_wx _ _ _)).sub (by
      simp only [List.cons_subset, List.nil_subset, and_true, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, true_or, or_true, List.cons_append, List.nil_append,
        dreg_mem 14 (by decide), dreg_mem 0 (by decide)])

/-- The carries from limb 0 to limb `n`. -/
theorem chain_ok : ∀ n ≤ 14, ∀ s : State, s.gpr .x22 = 0x1ffff →
    WP isa (.block ((List.range n).flatMap fun k => carryStep k (k + 1))) s fun s' =>
      regs s' = chainN (regs s) n ∧ Kp colRegs s s' ∧ s'.mem = s.mem
  | 0, _, s, _ => WP.block_nil ⟨rfl, Kp.refl _ _, rfl⟩
  | n + 1, hn, s, hm => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (chain_ok n (by omega) s hm) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    have hm₁ : s₁.gpr .x22 = 0x1ffff := by rw [k₁.gpr _ (by decide), hm]
    refine WP.mono (carryStep_ok (k := n) (k' := n + 1) (by omega) (by omega) (by omega) hm₁)
      fun s₂ ⟨e₂, k₂, m₂⟩ => ⟨?_, (k₁.trans k₂).sub
        (List.append_subset.mpr ⟨List.Subset.refl _, List.Subset.refl _⟩), m₂.trans m₁⟩
    rw [e₂, e₁]; rfl

theorem mask17_ok (s : State) :
    WP isa (.block mask17) s fun s' => s'.gpr .x22 = 0x1ffff ∧ Kp [.x22] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [mask17, runBlock_cons, exec_movz, runStep_some, exec_movk1, runBlock_nil,
    Option.some.injEq, exists_eq_left', gpr_wx_self]
  exact ⟨by decide, ((kp_wx s _ _).trans (kp_wx _ _ _)).sub (by sub_regs), rfl⟩

theorem const19_ok (s : State) :
    WP isa (.block const19) s fun s' => s'.gpr .x21 = 19 ∧ Kp [.x21] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [const19, runBlock_cons, exec_movz, runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left', gpr_wx_self]
  exact ⟨by decide, kp_wx s _ _, rfl⟩

/-- The registers of the field operations. -/
abbrev fieldRegs : List Reg := colRegs ++ [.x21, .x22]

theorem sub_field {W : List Reg} (h : ∀ r ∈ W, r ∈ fieldRegs) : W ⊆ fieldRegs := fun _ hr => h _ hr

/-- All the carries of a product. -/
theorem carry_ok {s : State} (h19 : s.gpr .x21 = 19) :
    WP isa (.block carry) s fun s' =>
      regs s' = carryF (regs s) ∧ Kp fieldRegs s s' ∧ s'.mem = s.mem := by
  rw [carry, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (mask17_ok s) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  have r₁ : regs s₁ = regs s := funext fun i => by
    simp only [regs]
    split
    · rename_i hi
      rw [v, k₁.gpr _ (by simpa using (dreg_facts i hi).2.2.2.2.1)]
    · rfl
  have h19₁ : s₁.gpr .x21 = 19 := by rw [k₁.gpr _ (by decide), h19]
  refine WP.block_append (WP.mono (chain_ok 14 (by decide) s₁ e₁) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  have hm₂ : s₂.gpr .x22 = 0x1ffff := by rw [k₂.gpr _ (by decide), e₁]
  have h19₂ : s₂.gpr .x21 = 19 := by rw [k₂.gpr _ (by decide), h19₁]
  refine WP.block_append (WP.mono (foldTop_ok hm₂ h19₂) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  have hm₃ : s₃.gpr .x22 = 0x1ffff := by rw [k₃.gpr _ (by decide), hm₂]
  refine WP.block_append (WP.mono (carryStep_ok (k := 0) (k' := 1) (by decide) (by decide) (by decide) hm₃)
    fun s₄ ⟨e₄, k₄, m₄⟩ => ?_)
  have hm₄ : s₄.gpr .x22 = 0x1ffff := by rw [k₄.gpr _ (by decide), hm₃]
  refine WP.mono (carryStep_ok (k := 1) (k' := 2) (by decide) (by decide) (by decide) hm₄)
    fun s₅ ⟨e₅, k₅, m₅⟩ => ⟨?_, ?_, by rw [m₅, m₄, m₃, m₂, m₁]⟩
  · rw [e₅, e₄, e₃, e₂, r₁]; rfl
  · refine (k₁.trans (k₂.trans (k₃.trans (k₄.trans k₅)))).sub fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with hr | hr | hr | hr | hr
    · exact Or.inr (Or.inr hr)
    all_goals exact Or.inl hr

/-! ## Stores -/

theorem wd_writeW (m : Mem) (b : Addr) {o off : Nat} (x : BitVec 64) (ho : Off o) (hoff : Off off) :
    wd (m.writeW (b + BitVec.ofNat 64 o) x) b off = if off = o then x.toNat else wd m b off := by
  have := ho.2; have := hoff.2
  by_cases h : off = o
  · subst h; rw [ite_eq_left rfl, wd, Mem.readW_writeW_self64]
  · rw [ite_eq_right h, wd, wd, Mem.readW_writeW_sep (Offset.sep b (by have := ho.1; have := hoff.1; omega)
      (by omega) (by omega)) (by decide)]

/-- The region of the element at `o`. -/
abbrev slotR (b : Addr) (o : Nat) : Region := ⟨b + BitVec.ofNat 64 o, 120⟩

theorem slot_contains (b : Addr) {o k : Nat} (ho : Slot o) (hk : k < 15) :
    (slotR b o).Contains (b + BitVec.ofNat 64 (o + 8 * k)) (64 / 8) :=
  Offset.contains b (by omega) (by omega) (by have := ho.2; omega)

theorem stores_ok {b : Addr} {o : Nat} (ho : Slot o) :
    ∀ n ≤ 15, ∀ s : State, Sc b s →
    WP isa (.block ((List.range n).map fun k => st (dreg k) (o + 8 * k))) s fun s' =>
      (∀ k < n, wd s'.mem b (o + 8 * k) = v s (dreg k)) ∧ Frame [slotR b o] s.mem s'.mem ∧
        Kp [] s s'
  | 0, _, s, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (stores_ok ho n (by omega) s hs) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (by decide)
    refine WP.block_cons_iff.mpr ⟨_, exec_st hs₁ _ (ho.off (by omega)), WP.block_nil ⟨fun k hk => ?_, ?_, ?_⟩⟩
    · simp only
      rw [wd_writeW _ _ _ (ho.off (by omega)) (ho.off (by omega))]
      by_cases hkn : k = n
      · subst hkn; rw [ite_eq_left rfl, k₁.gpr _ (by simp)]
      · rw [ite_eq_right (by omega)]; exact e₁ k (by omega)
    · exact f₁.writeW (List.mem_singleton_self _) _ (slot_contains b ho (by omega))
    · exact ⟨fun r _ => k₁.gpr r (by simp), k₁.rd, k₁.wr⟩

/-- The limbs stored at `o`. -/
theorem store_ok {b : Addr} {s : State} (hs : Sc b s) {o : Nat} (ho : Slot o) :
    WP isa (.block (store o)) s fun s' =>
      limbs s'.mem b o = regs s ∧ Frame [slotR b o] s.mem s'.mem ∧ Kp [] s s' :=
  WP.mono (stores_ok ho 15 (by decide) s hs) fun s' ⟨e, f, k⟩ => ⟨funext fun i => by
    simp only [limbs, regs]
    split
    · rename_i hi; exact e i hi
    · rfl, f, k⟩

/-! ## Multiplication -/

theorem regs_cols {b : Addr} {s s' : State} {a c : Nat}
    (h : ∀ k < 15, v s' (dreg k) = colM (limbs s.mem b a) (limbs s.mem b c) k) :
    regs s' = cols (limbs s.mem b a) (limbs s.mem b c) := funext fun k => by
  simp only [regs, cols]; split
  · rename_i hk; exact h k hk
  · rfl

/-- `[o] = [a] · [c]`. -/
theorem mul_ok {b : Addr} {s : State} (hs : Sc b s) {o a c : Nat} (ho : Slot o) (ha : Slot a)
    (hc : Slot c) :
    WP isa (.block (mul o a c)) s fun s' =>
      limbs s'.mem b o = mulF (limbs s.mem b a) (limbs s.mem b c) ∧ Frame [slotR b o] s.mem s'.mem ∧
        Kp fieldRegs s s' := by
  rw [mul, List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (const19_ok s) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  have hs₁ := hs.of_kp k₁ (by decide)
  refine WP.block_append (WP.mono (cols_ok ha hc 15 (by decide) s₁ hs₁ e₁) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  have hs₂ := hs₁.of_kp k₂ (by decide)
  have h19₂ : s₂.gpr .x21 = 19 := by rw [k₂.gpr _ (by decide), e₁]
  refine WP.block_append (WP.mono (carry_ok h19₂) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  have hs₃ := hs₂.of_kp k₃ (by decide)
  refine WP.mono (store_ok hs₃ ho) fun s₄ ⟨e₄, f₄, k₄⟩ => ⟨?_, ?_, ?_⟩
  · rw [e₄, e₃, regs_cols e₂, m₁]; rfl
  · rw [← m₁, ← m₂, ← m₃]; exact f₄
  · exact (k₁.trans (k₂.trans (k₃.trans k₄))).sub (List.append_subset.mpr ⟨by decide,
      List.append_subset.mpr ⟨List.subset_append_left _ _, by simp⟩⟩)

end VG.Proof.X25519.AArch64
