import VerifiedGarbage.Impl.Rc4.X86_64
import VerifiedGarbage.Proof.Rc4.Qword
import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! # RC4 on x86-64: the table lookup, a quadword at a time -/

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep sx_ofNat)

theorem eaAt (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  congr 1

theorem eaIdx (s : State) (b i : Reg) : s.ea (atIdx b i) = s.gpr b + s.gpr i := by
  simp only [State.ea, atIdx]
  rw [show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl,
    BitVec.add_zero]

theorem sx (n : Nat) (h : n < 2 ^ 31 := by decide) :
    (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := sx_ofNat h

theorem byte_addr (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- Steps a block of the RC4 code, from a state whose accesses the hypotheses permit. -/
syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic| (
      try unfold imm at *
      xrun [eaAt, eaIdx, sx 0, sx 1, sx 7, sx 8, sx 255, sx 256, List.cons_append,
        List.nil_append, $ls,*]))

/-! ## Visiting the quadwords -/

/-- The quadword holding byte `n`, once quadwords `0, …, k - 1` are visited. -/
def gather (m : Mem) (p : Addr) (n k : Nat) : BitVec 64 :=
  if n / 8 < k then m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 64 else 0

theorem gather_succ (m : Mem) (p : Addr) (n k : Nat) :
    gather m p n k ||| (if n / 8 = k then m.readW (p + BitVec.ofNat 64 (8 * k)) 64 else 0) =
      gather m p n (k + 1) := by
  unfold gather
  by_cases h0 : n / 8 < k
  · simp [h0, show ¬ n / 8 = k by omega, show n / 8 < k + 1 by omega]
  · by_cases h1 : n / 8 = k
    · subst h1; simp
    · simp [h0, h1, show ¬ n / 8 < k + 1 by omega]

/-- The mask `rowMask` leaves. -/
theorem row_mask (idx : Byte) {k : Nat} (hk : k < 32) (y : BitVec 64) :
    (0#64 - (BitVec.ofBool (decide ((idx.setWidth 64 ^^^ BitVec.ofNat 64 (8 * k)).toNat <
      (BitVec.ofNat 64 8).toNat))).setWidth 64) &&& y = if idx.toNat / 8 = k then y else 0 := by
  rw [borrow_mask, show (BitVec.ofNat 64 8).toNat = 8 from rfl]
  by_cases h : idx.toNat / 8 = k
  · rw [decide_eq_true ((row_hit idx hk).mpr h), ite_eq_left rfl, BitVec.allOnes_and, ite_eq_left h]
  · rw [decide_eq_false (fun h' => h ((row_hit idx hk).mp h')), ite_eq_right (by decide), ite_eq_right h]
    exact BitVec.zero_and

/-- The mask `laneMask` leaves. -/
theorem lane_mask (idx : Byte) {j : Nat} (hj : j < 8) (y : BitVec 64) :
    (0#64 - (BitVec.ofBool (decide (((idx.setWidth 64 &&& BitVec.ofNat 64 7) ^^^
      BitVec.ofNat 64 j).toNat < (BitVec.ofNat 64 1).toNat))).setWidth 64) &&& y =
      if idx.toNat % 8 = j then y else 0 := by
  rw [borrow_mask, show (BitVec.ofNat 64 1).toNat = 1 from rfl]
  by_cases h : idx.toNat % 8 = j
  · rw [decide_eq_true ((lane_hit idx hj).mpr h), ite_eq_left rfl, BitVec.allOnes_and, ite_eq_left h]
  · rw [decide_eq_false (fun h' => h ((lane_hit idx hj).mp h')), ite_eq_right (by decide), ite_eq_right h]
    exact BitVec.zero_and

theorem gather_step (s : State) (idx : Byte) {k : Nat} (hk : k < 32)
    (h9 : s.gpr .r9 = idx.setWidth 64)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (gatherStep k)) s fun t =>
      t.gpr .r11 = s.gpr .r11 |||
        (if idx.toNat / 8 = k then s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 64 else 0) ∧
      t.gpr .r9 = s.gpr .r9 ∧ t.gpr .rdi = s.gpr .rdi ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  unfold gatherStep rowMask
  rrun [h9, hr, sx (8 * k) (by omega)]
  rw [row_mask idx hk]

def GInv (s₀ : State) (idx : Byte) (k : Nat) (t : State) : Prop :=
  t.gpr .r11 = gather s₀.mem (s₀.gpr .rdi) idx.toNat k ∧ t.gpr .r9 = s₀.gpr .r9 ∧
    t.gpr .rdi = s₀.gpr .rdi ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr

theorem flatMap_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem gather_steps (s₀ : State) (idx : Byte) (h9 : s₀.gpr .r9 = idx.setWidth 64)
    (hr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi) 256) :
    ∀ n ≤ 32, ∀ s, GInv s₀ idx 0 s →
      WP isa (.block ((List.range n).flatMap gatherStep)) s (GInv s₀ idx n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨h11, h9', hdi, hm, hrd, hwr⟩ := ht
    have hq : InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [hrd, hwr, hdi]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hr
    refine WP.mono (gather_step t idx (by omega) (h9'.trans h9) hq) fun u hu => ?_
    obtain ⟨u11, u9, udi, um, urd, uwr⟩ := hu
    refine ⟨?_, u9.trans h9', udi.trans hdi, um.trans hm, urd.trans hrd, uwr.trans hwr⟩
    rw [u11, h11, hdi, hm, gather_succ]

/-! ## Picking the byte of the quadword -/

/-- The quadword shifted to byte `L`, once bytes `0, …, j - 1` are visited. -/
def pick (q : BitVec 64) (L j : Nat) : BitVec 64 := if L < j then q >>> (8 * L) else 0

theorem pick_succ (q : BitVec 64) (L j : Nat) :
    pick q L j ||| (if L = j then q >>> (8 * j) else 0) = pick q L (j + 1) := by
  unfold pick
  by_cases h0 : L < j
  · simp [h0, show ¬ L = j by omega, show L < j + 1 by omega]
  · by_cases h1 : L = j
    · subst h1; simp
    · simp [h0, h1, show ¬ L < j + 1 by omega]

theorem pick_step (s : State) (idx : Byte) {j : Nat} (hj : j < 8)
    (h9 : s.gpr .r9 = idx.setWidth 64) :
    WP isa (.block (pickStep j)) s fun t =>
      t.gpr .rax = s.gpr .rax ||| (if idx.toNat % 8 = j then s.gpr .r11 else 0) ∧
      t.gpr .r11 = s.gpr .r11 >>> 8 ∧
      t.gpr .r9 = s.gpr .r9 ∧ t.gpr .rdi = s.gpr .rdi ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  unfold pickStep laneMask
  rrun [h9, sx j (by omega)]
  rw [lane_mask idx hj]

def PInv (s₀ : State) (q : BitVec 64) (L j : Nat) (t : State) : Prop :=
  t.gpr .rax = pick q L j ∧ t.gpr .r11 = q >>> (8 * j) ∧ t.gpr .r9 = s₀.gpr .r9 ∧
    t.gpr .rdi = s₀.gpr .rdi ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr

theorem pick_steps (s₀ : State) (idx : Byte) (q : BitVec 64) (h9 : s₀.gpr .r9 = idx.setWidth 64) :
    ∀ n ≤ 8, ∀ s, PInv s₀ q (idx.toNat % 8) 0 s →
      WP isa (.block ((List.range n).flatMap pickStep)) s (PInv s₀ q (idx.toNat % 8) n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨hax, h11, h9', hdi, hm, hrd, hwr⟩ := ht
    refine WP.mono (pick_step t idx (by omega) (h9'.trans h9)) fun u hu => ?_
    obtain ⟨uax, u11, u9, udi, um, urd, uwr⟩ := hu
    refine ⟨?_, ?_, u9.trans h9', udi.trans hdi, um.trans hm, urd.trans hrd, uwr.trans hwr⟩
    · rw [uax, hax, h11, pick_succ]
    · rw [u11, h11, shr_byte]

/-! ## The lookup -/

theorem lookup_core (s : State) (idx : Byte) (h9 : s.gpr .r9 = idx.setWidth 64)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 256) :
    WP isa (.block lookup) s fun t =>
      t.gpr .rax = (s.mem (s.gpr .rdi + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.mem = s.mem := by
  have hn := idx.isLt
  simp only [lookup, List.append_assoc]
  rw [WP.block_append_iff]
  have h0 : WP isa (.block [.mov .r11 (imm 0)]) s (GInv s idx 0) := by
    rrun [GInv, gather, Nat.not_lt_zero]
  refine WP.mono h0 fun t ht => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gather_steps s idx h9 hr 32 (by decide) t ht) fun u hu => ?_
  obtain ⟨u11, u9, udi, um, urd, uwr⟩ := hu
  let q := s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (8 * (idx.toNat / 8))) 64
  have hq : u.gpr .r11 = q := by
    rw [u11]; unfold gather; rw [ite_eq_left (by omega)]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.mov .rax (imm 0)]) u (PInv s q (idx.toNat % 8) 0) := by
    rrun [PInv, pick, hq, u9, udi, um, urd, uwr, Nat.mul_zero, BitVec.ushiftRight_zero,
      Nat.not_lt_zero]
  refine WP.mono h1 fun v hv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pick_steps s idx q h9 8 (by decide) v hv) fun w hw => ?_
  obtain ⟨wax, _, _, _, wm, _, _⟩ := hw
  have hL : idx.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  rrun [wax, wm]
  unfold pick
  rw [ite_eq_left hL, qword_byte _ _ hL, row_lane]

end VG.Proof.Rc4.X86_64
