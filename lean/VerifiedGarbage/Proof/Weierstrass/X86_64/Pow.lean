import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bits
import VerifiedGarbage.Proof.Weierstrass.Pow

/-!
# Short Weierstrass curves on x86-64: powers

`pow P` leaves `[acc]` reading (in Montgomery form) as `[base]^e`, for the
exponent `e` whose bits are the table at `P.bits` (`pow_ok`): an iteration
squares the accumulator, multiplies it by the base into `[tmp]` and keeps
that product if the exponent's bit is set (`powBody_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- What a power writes: the accumulator, the temporary and the modulus's
temporary area. -/
def powW (P : PowCfg) : List (Nat × Nat) :=
  [(P.acc, 8 * P.M.n), (P.tmp, 8 * P.M.n), (P.M.tmp, 8 * P.M.n)]

/-- Where a power's slots and table are: in the working space, and what it
reads apart from what it writes. -/
structure PowLay (P : PowCfg) (size : Nat) : Prop where
  acc : P.acc + 8 * P.M.n ≤ size
  tmp : P.tmp + 8 * P.M.n ≤ size
  base : P.base + 8 * P.M.n ≤ size
  one : P.one + 8 * P.M.n ≤ size
  bits : P.bits + P.nbits ≤ size
  nbits : 1 ≤ P.nbits ∧ P.nbits < 2 ^ 31
  acc_tmp : P.acc + 8 * P.M.n ≤ P.tmp ∨ P.tmp + 8 * P.M.n ≤ P.acc
  acc_mtmp : P.acc + 8 * P.M.n ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.acc
  acc_one : P.acc + 8 * P.M.n ≤ P.one ∨ P.one + 8 * P.M.n ≤ P.acc
  base_w : ∀ w ∈ powW P, P.base + 8 * P.M.n ≤ w.1 ∨ w.1 + w.2 ≤ P.base
  bits_w : ∀ w ∈ powW P, P.bits + P.nbits ≤ w.1 ∨ w.1 + w.2 ≤ P.bits
  mo_w : ∀ w ∈ powW P, P.M.mo + 8 * P.M.n ≤ w.1 ∨ w.1 + w.2 ≤ P.M.mo

/-- The registers a power changes. -/
def powClob (n : Nat) : List Reg := .rbx :: clob n

theorem toM_one {m R : Nat} (hR : Nat.Coprime R m) : toM m R (R % m) = 1 := by
  unfold toM
  rw [ZMod.natCast_mod]
  exact ZMod.coe_mul_inv_eq_one R hR

theorem mov32Rbx_ok (s : State) {j : Nat} (hj : j < 2 ^ 31) :
    WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 j))]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 j ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem rbx_not_clob (n : Nat) : Reg.rbx ∉ clob n := by
  intro h
  simp only [clob, List.mem_cons] at h
  rcases h with h | h | h | h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · have := List.mem_of_mem_take h
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at this

/-- The loop's invariant at `rbx = j`: the accumulator reads as
`B^(e >>> j)`, for `B` what the base reads as at the start. -/
structure PowInv (P : PowCfg) (base : Addr) (size m e : Nat) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  rbx : s.gpr .rbx = BitVec.ofNat 64 j
  keep : KeepRegs (powClob P.M.n) s₀ s
  unch : Unch base (powW P) s₀.mem s.mem
  lt : wordsVal s.mem base P.acc P.M.n < m
  val : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) =
    toM m (2 ^ (64 * P.M.n)) (wordsVal s₀.mem base P.base P.M.n) ^ (e >>> j)

/-- An iteration. -/
theorem powBody_ok {P : PowCfg} {base : Addr} {size m e : Nat} (hL : PowLay P size)
    (hm : Nat.Coprime (2 ^ (64 * P.M.n)) m) {s₀ : State} (hM₀ : ModOk P.M size m s₀.mem base)
    (hB : wordsVal s₀.mem base P.base P.M.n < m)
    (hbits : ∀ t < P.nbits, s₀.mem (off base (P.bits + t)) = if e.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ P.nbits) (hI : PowInv P base size m e s₀ s j) :
    WP isa (powBody P) s fun s' =>
      PowInv P base size m e s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) := by
  have hn := hI.scr.nowrap
  have hnb := hL.nbits
  have hmo := hL.mo_w
  have hbw := hL.base_w
  have hacc := hL.acc
  have htmp := hL.tmp
  have hat := hL.acc_tmp
  have ham := hL.acc_mtmp
  have hmo' := hM₀.mo
  have hbase := hL.base
  have hbl := hL.bits
  have hM : ModOk P.M size m s.mem base :=
    ⟨hM₀.n0, hM₀.n7, hM₀.mo, hM₀.tmp, hM₀.sep,
      by rw [hI.unch.wordsVal hmo (by omega)]; exact hM₀.val, hM₀.inv⟩
  have hBs : wordsVal s.mem base P.base P.M.n = wordsVal s₀.mem base P.base P.M.n :=
    hI.unch.wordsVal hbw (by omega)
  -- `sub rbx, 1` and `acc = acc²`.
  rw [powBody]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (decRbx_ok s hj (by omega) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_
  have hs₁ := hI.scr.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine WP.mono (mul_ok hs₁ (hm₁ ▸ hM) hacc hacc hacc (by rw [hm₁]; exact hI.lt))
    fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_
  have hs₂ := k₂.scr hs₁
  have hM₂ : ModOk P.M size m s₂.mem base :=
    ⟨hM.n0, hM.n7, hM.mo, hM.tmp, hM.sep, by
      rw [k₂.unch.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hmo _ (by simp [powW])
        · exact hmo _ (by simp [powW])) (by omega), hm₁]; exact hM.val, hM.inv⟩
  have v₂ : toM m (2 ^ (64 * P.M.n)) (wordsVal s₂.mem base P.acc P.M.n) =
      toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) ^ 2 := by
    rw [toM_mul hm (e₂.trans (by rw [hm₁])), pow_two]
  have hB₂ : wordsVal s₂.mem base P.base P.M.n = wordsVal s₀.mem base P.base P.M.n := by
    rw [k₂.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hbw _ (by simp [powW])
      · exact hbw _ (by simp [powW])) (by omega), hm₁, hBs]
  -- `tmp = acc · base`.
  refine WP.seq ?_
  refine WP.mono (mul_ok hs₂ hM₂ htmp hacc hL.base (by rw [hB₂]; exact hB))
    fun s₃ ⟨k₃, lt₃, e₃⟩ => ?_
  have hs₃ := k₃.scr hs₂
  have hA₃ : wordsVal s₃.mem base P.acc P.M.n = wordsVal s₂.mem base P.acc P.M.n :=
    k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hat
      · exact ham) (by omega)
  have v₃ : toM m (2 ^ (64 * P.M.n)) (wordsVal s₃.mem base P.tmp P.M.n) =
      toM m (2 ^ (64 * P.M.n)) (wordsVal s₂.mem base P.acc P.M.n) *
        toM m (2 ^ (64 * P.M.n)) (wordsVal s₀.mem base P.base P.M.n) := by
    rw [toM_mul hm e₃, hB₂]
  -- The mask of bit `j - 1`, the selection, and `test rbx, rbx`.
  have hU₃ : Unch base (powW P) s₀.mem s₃.mem := by
    refine ((hI.unch.trans (by rw [← hm₁]; exact k₂.unch)).trans k₃.unch).mono fun w hw => ?_
    simp only [powW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  have hbyte : s₃.mem (off base (P.bits + (j - 1))) = if e.testBit (j - 1) then 1 else 0 := by
    rw [hU₃.byte (fun w hw => by have := hL.bits_w w hw; omega) (by omega), hbits _ (by omega)]
  have hrbx₃ : s₃.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₃.gpr _ (rbx_not_clob _), k₂.gpr _ (rbx_not_clob _), b₁]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (bitMask_bool_ok hs₃ hrbx₃ (by have := hL.bits; omega) hbyte)
    fun s₄ ⟨c₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (sel_ok (e.testBit (j - 1)) P.M.n hs₄ c₄ hacc hacc htmp (Or.inl (Nat.le_refl _))
    (by omega)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  have hrbx₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₅.gpr _ (by decide), k₄.1 _ (by decide), hrbx₃]
  refine WP.mono (testRbx_ok s₅ (by omega) hrbx₅) fun s₆ ⟨z₆, k₆⟩ => ⟨?_, z₆⟩
  have hm₆ : s₆.mem = s₅.mem := k₆.2.1
  have hm₄ : s₄.mem = s₃.mem := k₄.2.1
  refine ⟨hs₅.of_keeps k₆ (by decide), by rw [k₆.1 _ (by decide), hrbx₅], ?_, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · have hr' : r ∉ clob P.M.n := fun h => hr (List.mem_cons_of_mem _ h)
      have hrb : r ≠ .rbx := fun h => hr (h ▸ List.mem_cons_self ..)
      have hra : r ≠ .rax := fun h => hr' (h ▸ by simp [clob])
      have hrc : r ≠ .rcx := fun h => hr' (h ▸ by simp [clob])
      have hrd : r ≠ .rdx := fun h => hr' (h ▸ by simp [clob])
      rw [k₆.1 r (by simp), k₅.gpr r (by simp [hra, hrd]), k₄.1 r (by simp [hra, hrc]),
        k₃.gpr r hr', k₂.gpr r hr', k₁.1 r (by simp [hrb]), hI.keep.gpr r hr]
    · rw [k₆.2.2.1, k₅.rd, k₄.2.2.1, k₃.rd, k₂.rd, k₁.2.2.1, hI.keep.rd]
    · rw [k₆.2.2.2, k₅.wr, k₄.2.2.2, k₃.wr, k₂.wr, k₁.2.2.2, hI.keep.wr]
  · intro x hx
    rw [hm₆, O₅ x (hx _ (List.mem_cons_self ..)), hm₄]
    exact hU₃ x hx
  · rw [hm₆, e₅, hm₄]
    split
    · exact lt₃
    · rw [hA₃]; exact lt₂
  · rw [hm₆, e₅, hm₄, pow_shiftRight _ e (j - 1), Nat.sub_add_cancel hj, ← hI.val]
    split
    · rw [v₃, v₂]
    · rw [hA₃, v₂, mul_one]

/-- `[acc] = [base]^e` in Montgomery form, for the exponent `e < 2^nbits`
whose bits are the table at `P.bits`; only `powClob` and `powW` change. -/
theorem pow_ok {P : PowCfg} {base : Addr} {size m e : Nat} (hL : PowLay P size)
    (hm : Nat.Coprime (2 ^ (64 * P.M.n)) m) {s : State} (hs : Scr s base size)
    (hM : ModOk P.M size m s.mem base) (hB : wordsVal s.mem base P.base P.M.n < m)
    (hO : wordsVal s.mem base P.one P.M.n = 2 ^ (64 * P.M.n) % m)
    (hbits : ∀ t < P.nbits, s.mem (off base (P.bits + t)) = if e.testBit t then 1 else 0)
    (he : e < 2 ^ P.nbits) :
    WP isa (pow P) s fun s' => KeepRegs (powClob P.M.n) s s' ∧ Unch base (powW P) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ e := by
  have hn := hs.nowrap
  have hnb := hL.nbits
  have hm0 : 0 < m := m_pos hB
  rw [pow]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok P.M.n hs hL.acc hL.one (by have := hL.acc_one; omega))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  refine WP.mono (mov32Rbx_ok s₁ hnb.2) fun s₂ ⟨b₂, k₂⟩ => ?_
  refine countLoop_ok (Inv := fun j s' => PowInv P base size m e s s' j) (n := P.nbits)
    (fun j s' h1 h2 hi => powBody_ok hL hm hM hB hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.lt, by rw [hi.val, Nat.shiftRight_zero]⟩) hnb.1 ?_
  have hm₂ : s₂.mem = s₁.mem := k₂.2.1
  refine ⟨(hs.of_keepRegs k₁ (by decide)).of_keeps k₂ (by decide), b₂, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, by rw [k₂.2.2.1, k₁.rd], by rw [k₂.2.2.2, k₁.wr]⟩
    have hra : r ≠ .rax := fun h => hr (h ▸ by simp [powClob, clob])
    rw [k₂.1 r (fun h => hr (by simp at h; simp [h, powClob])), k₁.gpr r (by simp [hra])]
  · rw [hm₂]; exact O₁.unch.mono fun w hw => by simp at hw; simp [hw, powW]
  · rw [hm₂, e₁, hO]; exact Nat.mod_lt _ hm0
  · rw [hm₂, e₁, hO, toM_one hm, shiftRight_eq_zero he, pow_zero]

end VG.Proof.Weierstrass.X86_64
