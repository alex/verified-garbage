import VerifiedGarbage.Impl.Rc4.X86
import VerifiedGarbage.Proof.Rc4.Dword
import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run

/-! # RC4 on x86 (32-bit): the table lookup, a doubleword at a time -/

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

theorem eaAt (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem byte32 (b : Byte) : b.setWidth 32 = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- Steps a block of the RC4 code, from a state whose accesses the hypotheses permit. -/
syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic| (
      try unfold imm at *
      xrun [eaAt, List.cons_append, List.nil_append, $ls,*]))

/-- The address of doubleword `k` of the table at `P`, which does not wrap around. -/
theorem row_addr {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) {k : Nat} (hk : k < 64) :
    addr P (4 * k) = P.setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_of_fit (by omega)

/-! ## Visiting the doublewords -/

/-- The doubleword holding byte `n`, once doublewords `0, …, k - 1` are visited. -/
def gather (m : Mem) (p : Addr) (n k : Nat) : BitVec 32 :=
  if n / 4 < k then m.readW (p + BitVec.ofNat 64 (4 * (n / 4))) 32 else 0

theorem gather_succ (m : Mem) (p : Addr) (n k : Nat) :
    gather m p n k ||| (if n / 4 = k then m.readW (p + BitVec.ofNat 64 (4 * k)) 32 else 0) =
      gather m p n (k + 1) := by
  unfold gather
  by_cases h0 : n / 4 < k
  · simp [h0, show ¬ n / 4 = k by omega, show n / 4 < k + 1 by omega]
  · by_cases h1 : n / 4 = k
    · subst h1; simp
    · simp [h0, h1, show ¬ n / 4 < k + 1 by omega]

/-- The mask `rowMask` leaves. -/
theorem row_mask (idx : Byte) {k : Nat} (hk : k < 64) (y : BitVec 32) :
    (0#32 - (BitVec.ofBool (decide ((idx.setWidth 32 ^^^ BitVec.ofNat 32 (4 * k)).toNat <
      (BitVec.ofNat 32 4).toNat))).setWidth 32) &&& y = if idx.toNat / 4 = k then y else 0 := by
  rw [borrow_mask32, show (BitVec.ofNat 32 4).toNat = 4 from rfl]
  by_cases h : idx.toNat / 4 = k
  · rw [decide_eq_true ((row_hit32 idx hk).mpr h), ite_eq_left rfl, BitVec.allOnes_and,
      ite_eq_left h]
  · rw [decide_eq_false (fun h' => h ((row_hit32 idx hk).mp h')), ite_eq_right (by decide),
      ite_eq_right h]
    exact BitVec.zero_and

/-- The mask `laneMask` leaves. -/
theorem lane_mask (idx : Byte) {j : Nat} (hj : j < 4) (y : BitVec 32) :
    (0#32 - (BitVec.ofBool (decide (((idx.setWidth 32 &&& BitVec.ofNat 32 3) ^^^
      BitVec.ofNat 32 j).toNat < (BitVec.ofNat 32 1).toNat))).setWidth 32) &&& y =
      if idx.toNat % 4 = j then y else 0 := by
  rw [borrow_mask32, show (BitVec.ofNat 32 1).toNat = 1 from rfl]
  by_cases h : idx.toNat % 4 = j
  · rw [decide_eq_true ((lane_hit32 idx hj).mpr h), ite_eq_left rfl, BitVec.allOnes_and,
      ite_eq_left h]
  · rw [decide_eq_false (fun h' => h ((lane_hit32 idx hj).mp h')), ite_eq_right (by decide),
      ite_eq_right h]
    exact BitVec.zero_and

theorem gather_step (s : State) (idx : Byte) {k : Nat} (hk : k < 64)
    (hbp : s.gpr .ebp = idx.setWidth 32)
    (hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) (4 * k)) 4) :
    WP isa (.block (gatherStep k)) s fun t =>
      t.gpr .ecx = s.gpr .ecx |||
        (if idx.toNat / 4 = k then s.mem.readW (addr (s.gpr .edi) (4 * k)) 32 else 0) ∧
      t.gpr .ebp = s.gpr .ebp ∧ t.gpr .edi = s.gpr .edi ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  unfold gatherStep rowMask
  rrun [hbp, hr]
  rw [row_mask idx hk]

def GInv (s₀ : State) (idx : Byte) (k : Nat) (t : State) : Prop :=
  t.gpr .ecx = gather s₀.mem ((s₀.gpr .edi).setWidth 64) idx.toNat k ∧ t.gpr .ebp = s₀.gpr .ebp ∧
    t.gpr .edi = s₀.gpr .edi ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr

theorem flatMap_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem gather_steps (s₀ : State) (idx : Byte) (hbp : s₀.gpr .ebp = idx.setWidth 32)
    (hfit : (s₀.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .edi).setWidth 64) 256) :
    ∀ n ≤ 64, ∀ s, GInv s₀ idx 0 s →
      WP isa (.block ((List.range n).flatMap gatherStep)) s (GInv s₀ idx n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨h11, h9', hdi, hm, hrd, hwr⟩ := ht
    have hq : InRegions (t.rd ++ t.wr) (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [hrd, hwr, hdi, row_addr hfit (by omega)]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hr
    refine WP.mono (gather_step t idx (by omega) (h9'.trans hbp) hq) fun u hu => ?_
    obtain ⟨u11, u9, udi, um, urd, uwr⟩ := hu
    refine ⟨?_, u9.trans h9', udi.trans hdi, um.trans hm, urd.trans hrd, uwr.trans hwr⟩
    rw [u11, h11, hdi, hm, row_addr hfit (by omega), gather_succ]

/-! ## Picking the byte of the doubleword -/

/-- The doubleword shifted to byte `L`, once bytes `0, …, j - 1` are visited. -/
def pick (q : BitVec 32) (L j : Nat) : BitVec 32 := if L < j then q >>> (8 * L) else 0

theorem pick_succ (q : BitVec 32) (L j : Nat) :
    pick q L j ||| (if L = j then q >>> (8 * j) else 0) = pick q L (j + 1) := by
  unfold pick
  by_cases h0 : L < j
  · simp [h0, show ¬ L = j by omega, show L < j + 1 by omega]
  · by_cases h1 : L = j
    · subst h1; simp
    · simp [h0, h1, show ¬ L < j + 1 by omega]

theorem pick_step (s : State) (idx : Byte) {j : Nat} (hj : j < 4)
    (hbp : s.gpr .ebp = idx.setWidth 32) :
    WP isa (.block (pickStep j)) s fun t =>
      t.gpr .eax = s.gpr .eax ||| (if idx.toNat % 4 = j then s.gpr .ecx else 0) ∧
      t.gpr .ecx = s.gpr .ecx >>> 8 ∧
      t.gpr .ebp = s.gpr .ebp ∧ t.gpr .edi = s.gpr .edi ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  unfold pickStep laneMask
  rrun [hbp]
  rw [lane_mask idx hj]

def PInv (s₀ : State) (q : BitVec 32) (L j : Nat) (t : State) : Prop :=
  t.gpr .eax = pick q L j ∧ t.gpr .ecx = q >>> (8 * j) ∧ t.gpr .ebp = s₀.gpr .ebp ∧
    t.gpr .edi = s₀.gpr .edi ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr

theorem pick_steps (s₀ : State) (idx : Byte) (q : BitVec 32) (hbp : s₀.gpr .ebp = idx.setWidth 32) :
    ∀ n ≤ 4, ∀ s, PInv s₀ q (idx.toNat % 4) 0 s →
      WP isa (.block ((List.range n).flatMap pickStep)) s (PInv s₀ q (idx.toNat % 4) n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun t ht => ?_
    obtain ⟨hax, h11, h9', hdi, hm, hrd, hwr⟩ := ht
    refine WP.mono (pick_step t idx (by omega) (h9'.trans hbp)) fun u hu => ?_
    obtain ⟨uax, u11, u9, udi, um, urd, uwr⟩ := hu
    refine ⟨?_, ?_, u9.trans h9', udi.trans hdi, um.trans hm, urd.trans hrd, uwr.trans hwr⟩
    · rw [uax, hax, h11, pick_succ]
    · rw [u11, h11, shr_byte32]

/-! ## The lookup -/

theorem lookup_core (s : State) (idx : Byte) (hbp : s.gpr .ebp = idx.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) ((s.gpr .edi).setWidth 64) 256) :
    WP isa (.block lookup) s fun t =>
      t.gpr .eax = (s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 idx.toNat)).setWidth 32 ∧
      t.mem = s.mem := by
  have hn := idx.isLt
  simp only [lookup, List.append_assoc]
  rw [WP.block_append_iff]
  have h0 : WP isa (.block [.mov .ecx (imm 0)]) s (GInv s idx 0) := by
    rrun [GInv, gather, Nat.not_lt_zero]
  refine WP.mono h0 fun t ht => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gather_steps s idx hbp hfit hr 64 (by decide) t ht) fun u hu => ?_
  obtain ⟨u11, u9, udi, um, urd, uwr⟩ := hu
  let q := s.mem.readW ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 (4 * (idx.toNat / 4))) 32
  have hq : u.gpr .ecx = q := by
    rw [u11]; unfold gather; rw [ite_eq_left (by omega)]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.mov .eax (imm 0)]) u (PInv s q (idx.toNat % 4) 0) := by
    rrun [PInv, pick, hq, u9, udi, um, urd, uwr, Nat.mul_zero, BitVec.ushiftRight_zero,
      Nat.not_lt_zero]
  refine WP.mono h1 fun v hv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pick_steps s idx q hbp 4 (by decide) v hv) fun w hw => ?_
  obtain ⟨wax, _, _, _, wm, _, _⟩ := hw
  have hL : idx.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  rrun [wax, wm]
  unfold pick
  rw [ite_eq_left hL, dword_byte _ _ hL, row_lane32]

end VG.Proof.Rc4.X86
