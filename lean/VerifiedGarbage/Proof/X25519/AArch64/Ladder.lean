import VerifiedGarbage.Proof.X25519.AArch64.Slots
import VerifiedGarbage.Proof.X25519.Ladder

/-!
# X25519 on AArch64: the ladder

Untrusted: everything here is checked by Lean. One iteration of the ladder
(`step`) takes the ladder's variables in their slots from `ladderAfter k x1
(t + 1)` to `ladderAfter k x1 t`, for the bit `t` of the scalar stored at
`BITS + t`; the loop (`ladder`) runs it for `t = 254, …, 0`.
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## The bit and the mask -/

theorem maskB_of {x : Nat} (hx : x ≤ 1) :
    (0 : BitVec 64) - BitVec.ofNat 64 x = maskB (x == 1) := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> decide

theorem xor_le {a c : Nat} (ha : a ≤ 1) (hc : c ≤ 1) : a ^^^ c ≤ 1 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;>
    decide

theorem ofNat_xor {a c : Nat} (ha : a ≤ 1) (hc : c ≤ 1) :
    BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 c = BitVec.ofNat 64 (a ^^^ c) := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;>
    decide

/-- The address of bit `t`. -/
theorem bit_addr (b : Addr) (t : Nat) :
    b + BitVec.ofNat 64 t + BitVec.ofNat 64 BITS = b + BitVec.ofNat 64 (BITS + t) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]

theorem bit_in {b : Addr} {s : State} (hs : Sc b s) {t : Nat} (ht : t < 255) :
    InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (BITS + t)) 1 :=
  ⟨scR b, List.mem_append_right _ hs.wr, Offset.contains_base b (by simp only [BITS, slot, NSLOT]; omega)
    (by simp only [BITS, slot, NSLOT]; omega)⟩

/-- The start of an iteration: the bit `k_t` from `BITS`, `swap ^ k_t` into
`x20`, its mask into `x22`, and `swap = k_t`. -/
theorem head_ok {b : Addr} {s : State} (hs : Sc b s) {t sw kt : Nat} (ht : t < 255) (hsw : sw ≤ 1)
    (hkt : kt ≤ 1) (h23 : s.gpr .x23 = BitVec.ofNat 64 (t + 1)) (h24 : s.gpr .x24 = BitVec.ofNat 64 sw)
    (hbit : s.mem (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 kt) :
    WP isa (.block (([.subImm .x .x23 .x23 1, .add .x .x17 .x3 .x23, .ldrb .x19 .x17 BITS,
        .logic .eor .x .x20 .x24 .x19, .addImm .x .x24 .x19 0] : List Instr) ++ maskOf)) s fun s' =>
      s'.gpr .x23 = BitVec.ofNat 64 t ∧ s'.gpr .x24 = BitVec.ofNat 64 kt ∧
      s'.gpr .x22 = maskB ((sw ^^^ kt) == 1) ∧ Kp [.x23, .x17, .x19, .x20, .x24, .x22] s s' ∧
      s'.mem = s.mem := by
  have e23 : s.gpr .x23 - BitVec.ofNat 64 1 = BitVec.ofNat 64 t := by
    rw [h23, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), Nat.add_sub_cancel]
  have h1 : WP isa (.block [.subImm .x .x23 .x23 1, .add .x .x17 .x3 .x23]) s fun s₁ =>
      s₁.gpr .x23 = BitVec.ofNat 64 t ∧ s₁.gpr .x17 = b + BitVec.ofNat 64 t ∧ Kp [.x23, .x17] s s₁ ∧
        s₁.mem = s.mem := by
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_subImm_x (show 1 < 4096 by decide), runStep_some, exec_add_x, read_x,
      gpr_wx_self, gpr_wx_ne _ _ (show Reg.x3 ≠ .x23 by decide), runBlock_nil, Option.some.injEq,
      exists_eq_left', gpr_wx_ne _ _ (show Reg.x23 ≠ .x17 by decide), hs.x3, e23]
    exact ⟨trivial, trivial, ((kp_wx s _ _).trans (kp_wx _ _ _)).sub (by sub_regs), rfl⟩
  rw [show ([.subImm .x .x23 .x23 1, .add .x .x17 .x3 .x23, .ldrb .x19 .x17 BITS,
        .logic .eor .x .x20 .x24 .x19, .addImm .x .x24 .x19 0] ++ maskOf : List Instr) =
      ([.subImm .x .x23 .x23 1, .add .x .x17 .x3 .x23] : List Instr) ++
      ([.ldrb .x19 .x17 BITS, .logic .eor .x .x20 .x24 .x19, .addImm .x .x24 .x19 0,
        .movz .x .x22 0 0, .sub .x .x22 .x22 .x20] : List Instr) from rfl]
  refine WP.block_append (WP.mono h1 fun s₁ ⟨e₁, f₁, k₁, m₁⟩ => ?_)
  have hs₁ := hs.of_kp k₁ (by decide)
  have h24₁ : s₁.gpr .x24 = BitVec.ofNat 64 sw := by rw [k₁.gpr _ (by decide), h24]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_ldrb (by decide) (by rw [f₁, bit_addr]; exact bit_in hs₁ ht), runStep_some]
  have hk : ((s₁.mem.read (b + BitVec.ofNat 64 (BITS + t)) 1).setWidth 32).setWidth 64 = BitVec.ofNat 64 kt := by
    rw [read1_toNat, m₁, hbit]
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  simp only [runBlock_cons, runStep_some, exec_eor_x, exec_addImm_x (show 0 < 4096 by decide), exec_movz,
    exec_sub_x, read_x, runBlock_nil, Option.some.injEq, exists_eq_left', f₁, bit_addr, gpr_wx_self,
    gpr_ww_self, gpr_wx_ne _ _ (show Reg.x23 ≠ .x22 by decide), gpr_wx_ne _ _ (show Reg.x24 ≠ .x22 by decide),
    gpr_wx_ne _ _ (show Reg.x20 ≠ .x22 by decide), gpr_wx_ne _ _ (show Reg.x20 ≠ .x24 by decide),
    gpr_wx_ne _ _ (show Reg.x19 ≠ .x20 by decide),
    gpr_wx_ne _ _ (show Reg.x23 ≠ .x24 by decide), gpr_wx_ne _ _ (show Reg.x23 ≠ .x20 by decide),
    gpr_ww_ne _ _ (show Reg.x23 ≠ .x19 by decide), gpr_ww_ne _ _ (show Reg.x24 ≠ .x19 by decide), hk, e₁, h24₁]
  refine ⟨trivial, by rw [BitVec.add_zero], ?_, ?_, ?_⟩
  · rw [ofNat_xor hsw hkt, show BitVec.setWidth 64 (0 : BitVec 16) = 0 from rfl, maskB_of (xor_le hsw hkt)]
  · exact (k₁.trans ((((kp_ww _ _ _).trans (kp_wx _ _ _)).trans (kp_wx _ _ _)).trans
      ((kp_wx _ _ _).trans (kp_wx _ _ _)))).sub (by sub_regs)
  · simp only [mem_wx, mem_ww, m₁]

end VG.Proof.X25519.AArch64

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## One iteration -/

/-- The ladder's variables in their slots: `x_1, x_2, z_2, x_3, z_3` in slots 0 to 4. -/
def lvals (x1 : Fe) (st : Ladder) (n : Nat) : Fe :=
  if n = 0 then x1 else if n = 1 then st.x2 else if n = 2 then st.z2 else if n = 3 then st.x3 else st.z3

/-- Slots 0 to 4 have limbs below `2¹⁸`. -/
def lbnds (n : Nat) : Option Nat := if n < 5 then some 18 else none

theorem Sl.weaken {m : Mem} {b : Addr} {vals vals' : Nat → Fe} {bnds bnds' : Nat → Option Nat}
    (h : Sl m b vals bnds) (hw : ∀ n < 15, ∀ j, bnds' n = some j → bnds n = some j ∧ vals' n = vals n) :
    Sl m b vals' bnds' := fun n hn j hj => by
  obtain ⟨h1, h2⟩ := hw n hn j hj
  rw [h2]; exact h n hn j h1

/-- Evaluates the slots' values after an operation, so that they refer to the
earlier ones only through their values. -/
macro "vsimp" " at " h:ident : tactic => `(tactic| simp only [Function.update_apply, lvals, ite_true, ite_false,
  Nat.reduceEqDiff] at $h:ident)

/-- The field operations of an iteration, after the swaps' mask `x22`. -/
theorem ops_ok {b : Addr} {s₀ s : State} {x1 : Fe} {st : Ladder} (h : Inv b s₀ s (lvals x1 st) lbnds)
    {sw : Nat} (hm : s.gpr .x22 = maskB (sw == 1)) :
    WP isa (.block (cswap X2 X3 ++ cswap Z2 Z3 ++
      add A X2 Z2 ++ mul AA A A ++ sub B X2 Z2 ++ mul BB B B ++ sub E AA BB ++
      add C X3 Z3 ++ sub D X3 Z3 ++ mul DA D A ++ mul CB C B ++
      add X3 DA CB ++ mul X3 X3 X3 ++ sub Z3 DA CB ++ mul Z3 Z3 Z3 ++ mul Z3 X1 Z3 ++
      mul X2 AA BB ++ mulSmall Z2 E ++ add Z2 AA Z2 ++ mul Z2 E Z2)) s fun s' =>
      let x2 := (cswap sw st.x2 st.x3).1
      let x3 := (cswap sw st.x2 st.x3).2
      let z2 := (cswap sw st.z2 st.z3).1
      let z3 := (cswap sw st.z2 st.z3).2
      let A := x2 + z2
      let AA := A * A
      let B := x2 - z2
      let BB := B * B
      let E := AA - BB
      let C := x3 + z3
      let D := x3 - z3
      let DA := D * A
      let CB := C * B
      Inv b s₀ s' (lvals x1 ⟨AA * BB, E * (AA + a24 * E), (DA + CB) * (DA + CB),
        x1 * ((DA - CB) * (DA - CB)), 0⟩) lbnds := by
  simp only [X1, X2, Z2, X3, Z3, A, B, C, D, AA, BB, E, DA, CB, List.append_assoc]
  refine WP.block_append (WP.mono (cswap_inv h (x := 1) (y := 3) (by decide) (by decide) (by decide)
    (k := 18) rfl rfl hm) fun s₁ ⟨h₁, g₁⟩ => ?_)
  vsimp at h₁
  have hm₁ : s₁.gpr .x22 = maskB (sw == 1) := by rw [g₁, hm]
  refine WP.block_append (WP.mono (cswap_inv h₁ (x := 2) (y := 4) (by decide) (by decide) (by decide)
    (k := 18) rfl rfl hm₁) fun s₂ ⟨h₂, _⟩ => ?_)
  vsimp at h₂
  refine WP.block_append (WP.mono (add_inv h₂ (o := 5) (a := 1) (c := 2) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₃ h₃ => ?_)
  vsimp at h₃
  refine WP.block_append (WP.mono (mul_inv h₃ (o := 9) (a := 5) (c := 5) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₄ h₄ => ?_)
  vsimp at h₄
  refine WP.block_append (WP.mono (sub_inv h₄ (o := 6) (a := 1) (c := 2) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₅ h₅ => ?_)
  vsimp at h₅
  refine WP.block_append (WP.mono (mul_inv h₅ (o := 10) (a := 6) (c := 6) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₆ h₆ => ?_)
  vsimp at h₆
  refine WP.block_append (WP.mono (sub_inv h₆ (o := 11) (a := 9) (c := 10) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₇ h₇ => ?_)
  vsimp at h₇
  refine WP.block_append (WP.mono (add_inv h₇ (o := 7) (a := 3) (c := 4) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₈ h₈ => ?_)
  vsimp at h₈
  refine WP.block_append (WP.mono (sub_inv h₈ (o := 8) (a := 3) (c := 4) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₉ h₉ => ?_)
  vsimp at h₉
  refine WP.block_append (WP.mono (mul_inv h₉ (o := 12) (a := 8) (c := 5) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₁₀ h₁₀ => ?_)
  vsimp at h₁₀
  refine WP.block_append (WP.mono (mul_inv h₁₀ (o := 13) (a := 7) (c := 6) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₁₁ h₁₁ => ?_)
  vsimp at h₁₁
  refine WP.block_append (WP.mono (add_inv h₁₁ (o := 3) (a := 12) (c := 13) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₁₂ h₁₂ => ?_)
  vsimp at h₁₂
  refine WP.block_append (WP.mono (mul_inv h₁₂ (o := 3) (a := 3) (c := 3) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₁₃ h₁₃ => ?_)
  vsimp at h₁₃
  refine WP.block_append (WP.mono (sub_inv h₁₃ (o := 4) (a := 12) (c := 13) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₁₄ h₁₄ => ?_)
  vsimp at h₁₄
  refine WP.block_append (WP.mono (mul_inv h₁₄ (o := 4) (a := 4) (c := 4) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₁₅ h₁₅ => ?_)
  vsimp at h₁₅
  refine WP.block_append (WP.mono (mul_inv h₁₅ (o := 4) (a := 0) (c := 4) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₁₆ h₁₆ => ?_)
  vsimp at h₁₆
  refine WP.block_append (WP.mono (mul_inv h₁₆ (o := 1) (a := 9) (c := 10) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₁₇ h₁₇ => ?_)
  vsimp at h₁₇
  refine WP.block_append (WP.mono (mulSmall_inv h₁₇ (o := 2) (a := 11) (by decide) (by decide)
    (ka := 26) rfl (by decide)) fun s₁₈ h₁₈ => ?_)
  vsimp at h₁₈
  refine WP.block_append (WP.mono (add_inv h₁₈ (o := 2) (a := 9) (c := 2) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₁₉ h₁₉ => ?_)
  vsimp at h₁₉
  refine WP.mono (mul_inv h₁₉ (o := 2) (a := 11) (c := 2) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₂₀ h₂₀ => ?_
  vsimp at h₂₀
  refine ⟨h₂₀.sc, h₂₀.sl.weaken fun n hn j hj => ?_, h₂₀.kp, h₂₀.fr⟩
  simp only [lbnds] at hj
  split at hj
  · rename_i h5
    cases hj
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) with rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨rfl, ?_⟩ <;> simp only [Function.update_apply, lvals, ite_true, ite_false,
        Nat.reduceEqDiff, OfNat.ofNat_ne_zero, zero_ne_one]
  · cases hj

end VG.Proof.X25519.AArch64

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-- The registers the ladder writes. -/
abbrev loopRegs : List Reg := fieldRegs ++ [.x23, .x24]

theorem lvals_congr (x1 : Fe) {st st' : Ladder} (h2 : st.x2 = st'.x2) (hz2 : st.z2 = st'.z2)
    (h3 : st.x3 = st'.x3) (hz3 : st.z3 = st'.z3) : lvals x1 st = lvals x1 st' := by
  funext n; simp only [lvals, h2, hz2, h3, hz3]

/-- A byte of `BITS` is not in the slots. -/
theorem bits_frame {b : Addr} {m m' : Mem} (hf : Frame [slotArea b] m m') {t : Nat} (ht : t < 256) :
    m' (b + BitVec.ofNat 64 (BITS + t)) = m (b + BitVec.ofNat 64 (BITS + t)) := by
  refine hf _ fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  intro hc
  have := Offset.sep b (d := 64) (n := 1920) (e := BITS + t) (k := 1)
    (by simp only [BITS, slot, NSLOT]; omega) (by decide) (by simp only [BITS, slot, NSLOT]; omega)
  exact this _ hc (by simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.lt_one_iff])

/-- One iteration of the ladder, for the bit `t`. -/
theorem step_ok {b : Addr} {s : State} {k : Nat} {x1 : Fe} {t : Nat} (ht : t < 255)
    (hsc : Sc b s) (hsl : Sl s.mem b (lvals x1 (ladderAfter k x1 (t + 1))) lbnds)
    (h23 : s.gpr .x23 = BitVec.ofNat 64 (t + 1))
    (h24 : s.gpr .x24 = BitVec.ofNat 64 (ladderAfter k x1 (t + 1)).swap)
    (hbit : s.mem (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (bit k t)) :
    WP isa (.block step) s fun s' =>
      Sc b s' ∧ Sl s'.mem b (lvals x1 (ladderAfter k x1 t)) lbnds ∧
      s'.gpr .x23 = BitVec.ofNat 64 t ∧ s'.gpr .x24 = BitVec.ofNat 64 (ladderAfter k x1 t).swap ∧
      Kp loopRegs s s' ∧ Frame [slotArea b] s.mem s'.mem := by
  have hsw := ladderAfter_swap_le k x1 (n := t + 1) (by omega)
  have hkt := bit_le k t
  have e : step = ([.subImm .x .x23 .x23 1, .add .x .x17 .x3 .x23, .ldrb .x19 .x17 BITS,
      .logic .eor .x .x20 .x24 .x19, .addImm .x .x24 .x19 0] ++ maskOf) ++ (cswap X2 X3 ++ cswap Z2 Z3 ++
      add A X2 Z2 ++ mul AA A A ++ sub B X2 Z2 ++ mul BB B B ++ sub E AA BB ++
      add C X3 Z3 ++ sub D X3 Z3 ++ mul DA D A ++ mul CB C B ++
      add X3 DA CB ++ mul X3 X3 X3 ++ sub Z3 DA CB ++ mul Z3 Z3 Z3 ++ mul Z3 X1 Z3 ++
      mul X2 AA BB ++ mulSmall Z2 E ++ add Z2 AA Z2 ++ mul Z2 E Z2) := by
    simp only [step, List.append_assoc]
  rw [e]
  refine WP.block_append (WP.mono (head_ok hsc ht hsw hkt h23 h24 hbit) fun s₁ ⟨e23, e24, e22, k₁, m₁⟩ => ?_)
  have hI : Inv b s₁ s₁ (lvals x1 (ladderAfter k x1 (t + 1))) lbnds :=
    ⟨hsc.of_kp k₁ (by decide), by rw [m₁]; exact hsl, Kp.refl _ _, Frame.refl _ _⟩
  refine WP.mono (ops_ok hI e22) fun s₂ h₂ => ?_
  have hst := ladderAfter_step k x1 ht
  refine ⟨h₂.sc, ?_, ?_, ?_, (k₁.trans h₂.kp).sub (List.append_subset.mpr ⟨by decide,
    List.subset_append_left _ _⟩), ?_⟩
  · rw [hst, ladderStep_eq]
    exact h₂.sl
  · rw [h₂.kp.gpr _ (by decide), e23]
  · rw [h₂.kp.gpr _ (by decide), e24, hst, ladderStep_eq]
  · rw [← m₁]; exact h₂.fr

/-- The ladder's loop, from the counter `n`: the iterations for the bits `n - 1` down to 0. -/
theorem loop_ok {b : Addr} {s₀ : State} {k : Nat} {x1 : Fe}
    (hbits : ∀ t < 255, s₀.mem (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (bit k t)) :
    ∀ n, ∀ s, (1 ≤ n ∧ n ≤ 255 ∧ Sc b s ∧ Sl s.mem b (lvals x1 (ladderAfter k x1 n)) lbnds ∧
      s.gpr .x23 = BitVec.ofNat 64 n ∧ s.gpr .x24 = BitVec.ofNat 64 (ladderAfter k x1 n).swap ∧
      Kp loopRegs s₀ s ∧ Frame [slotArea b] s₀.mem s.mem) →
    WP isa (.loop (.block step) (.nonzero .x .x23)) s fun s' =>
      Sc b s' ∧ Sl s'.mem b (lvals x1 (ladderAfter k x1 0)) lbnds ∧
      s'.gpr .x24 = BitVec.ofNat 64 (ladderAfter k x1 0).swap ∧ Kp loopRegs s₀ s' ∧
      Frame [slotArea b] s₀.mem s'.mem := by
  refine WP.loop (M := isa) (fun n s => 1 ≤ n ∧ n ≤ 255 ∧ Sc b s ∧
      Sl s.mem b (lvals x1 (ladderAfter k x1 n)) lbnds ∧
      s.gpr .x23 = BitVec.ofNat 64 n ∧ s.gpr .x24 = BitVec.ofNat 64 (ladderAfter k x1 n).swap ∧
      Kp loopRegs s₀ s ∧ Frame [slotArea b] s₀.mem s.mem) ?_
  rintro n s ⟨h1, h255, hsc, hsl, h23, h24, hkp, hfr⟩
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  refine WP.mono (step_ok (t := t) (by omega) hsc hsl h23 h24
    (by rw [bits_frame hfr (by omega)]; exact hbits t (by omega))) fun s' ⟨sc', sl', e23, e24, kp', fr'⟩ => ?_
  have hev : isa.eval (.nonzero .x .x23) s' = some (BitVec.ofNat 64 t != 0) := by
    simp only [eval, read_x, e23]
  have hkp : Kp loopRegs s₀ s' := (hkp.trans kp').sub (List.append_subset.mpr
    ⟨List.Subset.refl _, List.Subset.refl _⟩)
  have hfr' : Frame [slotArea b] s₀.mem s'.mem := hfr.trans fr'
  by_cases ht : t = 0
  · subst ht
    exact .inl ⟨by rw [hev]; rfl, sc', sl', e24, hkp, hfr'⟩
  · refine .inr ⟨?_, t, by omega, by omega, by omega, sc', sl', e23, e24, hkp, hfr'⟩
    rw [hev]
    have : BitVec.ofNat 64 t ≠ 0 := fun h => ht (by
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this)
    simpa using this

/-- The ladder, from its initial state in the slots. -/
theorem ladder_ok {b : Addr} {s : State} {k : Nat} {x1 : Fe}
    (hsc : Sc b s) (hsl : Sl s.mem b (lvals x1 (init x1)) lbnds)
    (hbits : ∀ t < 255, s.mem (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (bit k t)) :
    WP isa ladder s fun s' => Sc b s' ∧ Sl s'.mem b (lvals x1 (ladderAfter k x1 0)) lbnds ∧
      s'.gpr .x24 = BitVec.ofNat 64 (ladderAfter k x1 0).swap ∧ Kp loopRegs s s' ∧
      Frame [slotArea b] s.mem s'.mem := by
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => s₁.gpr .x23 = BitVec.ofNat 64 255 ∧ s₁.gpr .x24 = 0 ∧
    Kp [.x23, .x24] s s₁ ∧ s₁.mem = s.mem) ?_ fun s₁ ⟨e23, e24, k₁, m₁⟩ => ?_)
  · apply WP.of_runBlock
    simp only [runBlock_cons, exec_movz, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left',
      gpr_wx_self, gpr_wx_ne _ _ (show Reg.x23 ≠ .x24 by decide)]
    exact ⟨by decide, by decide, ((kp_wx s _ _).trans (kp_wx _ _ _)).sub (by sub_regs), rfl⟩
  · refine WP.mono (loop_ok (s₀ := s) hbits 255 s₁ ⟨by decide, by decide, hsc.of_kp k₁ (by decide),
      by rw [m₁, ladderAfter_255]; exact hsl, e23, by rw [e24, ladderAfter_255]; rfl, k₁.sub (by decide),
      by rw [m₁]; exact Frame.refl _ _⟩) fun s' h => h

end VG.Proof.X25519.AArch64
