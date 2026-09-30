import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Powers

/-!
# Poly1305 on x86-64 with AVX2: groups of four blocks

Untrusted: everything here is checked by Lean. Each group of four blocks is
added to the lanes of `H` and multiplied by `r⁴` (Horner's rule in four
lanes, `Horner.lean`); the last group is multiplied lane by lane by `r⁴`,
`r³`, `r²` and `r`, after which the sum of the lanes is the accumulator.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2
open VG.Spec.Poly1305 (P leNum bytesAt)
open VG.Proof.Poly1305 (mv lanes absorbAll)

/-- Block `k` of the group at `rsi`. -/
def blk (s : State) (k : Nat) : List Byte := bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (16 * k)) 16

theorem blk_length (s : State) (k : Nat) : (blk s k).length = 16 := Poly1305.length_bytesAt _ _ _

theorem blk_mv (s : State) (k : Nat) : mv (blk s k) = blo s k + 2 ^ 64 * bhi s k + 2 ^ 128 := by
  rw [mv, Poly1305.leNum_append, blk, Poly1305.length_bytesAt, Poly1305.leNum_bytesAt_16]
  have e₁ : s.gpr .rsi + BitVec.ofNat 64 (16 * k) = s.gpr .rsi + BitVec.ofNat 64 (8 * (2 * k)) := by
    rw [show 16 * k = 8 * (2 * k) by omega]
  have e₂ : s.gpr .rsi + BitVec.ofNat 64 (16 * k) + 8 = s.gpr .rsi + BitVec.ofNat 64 (8 * (2 * k + 1)) := by
    rw [BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add,
      show 16 * k + 8 = 8 * (2 * k + 1) by omega]
  rw [e₂, e₁]
  simp only [blo, bhi, envOf]
  rfl

/-- The group at `rsi`, block by block. -/
theorem group_bytes (s : State) :
    bytesAt s.mem (s.gpr .rsi) 64 = blk s 0 ++ blk s 1 ++ blk s 2 ++ blk s 3 := by
  rw [show 64 = 48 + 16 from rfl, Poly1305.bytesAt_add, show 48 = 32 + 16 from rfl, Poly1305.bytesAt_add,
    show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add]
  simp only [blk]
  rw [show BitVec.ofNat 64 (16 * 0) = 0#64 from rfl, BitVec.add_zero]

/-- What holds of the vector registers between groups: `Y` holds the powers
of `R`, and the lanes of `H` (limbs below `2²⁷`) the accumulator `X`, after
Horner's rule in four lanes. -/
structure LaneInv (R X : Nat) (s : State) : Prop where
  y : YInv s R
  hb : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 27
  acc : lanes R (Limbs26.val (hv s 0)) (Limbs26.val (hv s 1)) (Limbs26.val (hv s 2))
    (Limbs26.val (hv s 3)) ≡ R ^ 4 * X [MOD P]

theorem YInv.of_y {s s' : State} {R : Nat} (h : YInv s R) (hy : ∀ i < 5, ∀ k < 4, qw s' (yreg i) k = qw s (yreg i) k) :
    YInv s' R := by
  have el : ∀ k < 4, yl s' k = yl s k := fun k hk => ext5 (fun _ h => yl_ge _ _ h) (fun _ h => yl_ge _ _ h)
    fun i hi => by simp only [yl, hy i hi k hk]
  have eh : ∀ k < 4, yh s' k = yh s k := fun k hk => ext5 (fun _ h => yh_ge _ _ h) (fun _ h => yh_ge _ _ h)
    fun i hi => by simp only [yh, hy i hi k hk]
  exact ⟨fun k hk => by rw [el k hk]; exact h.lo k hk, fun k hk => by rw [eh k hk]; exact h.hi k hk,
    fun k hk => by rw [el k hk]; exact h.lob k hk, fun k hk => by rw [eh k hk]; exact h.hib k hk⟩

/-- `addGroup`, then `mul` by `Y`'s low doublewords: lane `k` becomes
`(V_k + m_k) · Y_k`. -/
theorem addMul_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hr9 : s.gpr .r9 = 0x1000000) (hc : Ctx s)
    (hb : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 27) (hy : ∀ k < 4, ∀ i < 5, yl s k i < 2 ^ 27) :
    WP isa (.block (addGroup ++ mul)) s fun s' => vec s s' = s' ∧
      (∀ i < 5, ∀ k < 4, qw s' (yreg i) k = qw s (yreg i) k) ∧ (∀ k < 4, ∀ i < 5, hv s' k i < 2 ^ 27) ∧
      ∀ k < 4, Limbs26.val (hv s' k) ≡ (Limbs26.val (hv s k) + mv (blk s k)) * Limbs26.val (yl s k) [MOD P] := by
  refine WP.block_append (WP.mono (addGroup_ok ⟨hr9, hc, hb⟩) fun s₁ A => ?_)
  have hyl : ∀ k < 4, yl s₁ k = yl s k := fun k hk => ext5 (fun _ h => yl_ge _ _ h) (fun _ h => yl_ge _ _ h)
    fun i hi => by simp only [yl, A.y i hi k hk]
  refine WP.mono (mul_ok ⟨by rw [vec_gpr A.vec, hr8], A.hb, fun k hk i hi => by rw [hyl k hk]; exact hy k hk i hi⟩)
    fun s₂ M => ⟨vec_trans A.vec M.vec, fun i hi k hk => by rw [M.y i hi k hk, A.y i hi k hk], M.hb,
      fun k hk => ?_⟩
  rw [val_congr (M.h k hk), blk_mv, ← A.h k hk, ← hyl k hk]
  exact Limbs26.mul_mod _ _

/-- A group before the last: the invariant for the blocks so far and the group. -/
theorem group_ok {R X : Nat} {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hr9 : s.gpr .r9 = 0x1000000)
    (hc : Ctx s) (hI : LaneInv R X s) :
    WP isa (.block (addGroup ++ mul)) s fun s' => vec s s' = s' ∧
      LaneInv R (absorbAll R X (bytesAt s.mem (s.gpr .rsi) 64)) s' := by
  refine WP.mono (addMul_ok hr8 hr9 hc hI.hb hI.y.lob) fun s' ⟨hv', hy, hb, he⟩ => ⟨hv', hI.y.of_y hy, hb, ?_⟩
  rw [group_bytes]
  exact Poly1305.horner_step (blk_length s 0) (blk_length s 1) (blk_length s 2) (blk_length s 3) hI.acc
    ((he 0 (by decide)).trans (Nat.ModEq.mul_left _ (hI.y.lo 0 (by decide))))
    ((he 1 (by decide)).trans (Nat.ModEq.mul_left _ (hI.y.lo 1 (by decide))))
    ((he 2 (by decide)).trans (Nat.ModEq.mul_left _ (hI.y.lo 2 (by decide))))
    ((he 3 (by decide)).trans (Nat.ModEq.mul_left _ (hI.y.lo 3 (by decide))))

/-! ## The last group -/

def shY : List Instr := (List.range 5).map fun i => srl (yreg i) (yreg i) 32

theorem last_eq : last = addGroup ++ (shY ++ mul) := rfl

def shS : Sym := (Sym.init.run false shY).get (by decide +kernel)
theorem shS_eq : Sym.init.run false shY = some shS := (Option.some_get _).symm
theorem shS_shape : ∀ i < 5, shS.reg (xi (yreg i)) = .shr (.reg (xi (yreg i))) 32 ∧
    shS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem shY_ok (s : State) :
    WP isa (.block shY) s fun s' => vec s s' = s' ∧ (∀ k < 4, ∀ i < 5, hv s' k i = hv s k i ∧
      yl s' k i = yh s k i) := by
  refine WP.mono (run_ok (by intro h; cases h) shS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ⟨?_, ?_⟩⟩
  · simp only [hv]; rw [h.reg _ k hk, (shS_shape i hi).2]; simp only [Q.eval, xr_xi]
  · simp only [yl, yh]
    rw [h.natw _ hk, (shS_shape i hi).1]
    simp only [Q.natw, envOf_v]
    have := (qw s (yreg i) k).isLt
    omega

/-- The last group: lane `k` multiplied by `r^(4-k)`, and the lanes' sum is
the accumulator. -/
theorem last_ok {R X : Nat} {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hr9 : s.gpr .r9 = 0x1000000)
    (hc : Ctx s) (hI : LaneInv R X s) :
    WP isa (.block last) s fun s' => vec s s' = s' ∧ (∀ k < 4, ∀ i < 5, hv s' k i < 2 ^ 27) ∧
      Limbs26.val (hv s' 0) + Limbs26.val (hv s' 1) + Limbs26.val (hv s' 2) + Limbs26.val (hv s' 3) ≡
        absorbAll R X (bytesAt s.mem (s.gpr .rsi) 64) [MOD P] := by
  rw [last_eq]
  refine WP.block_append (WP.mono (addGroup_ok ⟨hr9, hc, hI.hb⟩) fun s₁ A => ?_)
  have Y₁ := hI.y.of_y A.y
  refine WP.block_append (WP.mono (shY_ok s₁) fun s₂ ⟨v₂, e₂⟩ => ?_)
  have hH : ∀ k < 4, hv s₂ k = hv s₁ k := fun k hk => ext5 (fun _ h => hv_ge _ _ h) (fun _ h => hv_ge _ _ h)
    fun i hi => (e₂ k hk i hi).1
  have hY : ∀ k < 4, yl s₂ k = yh s₁ k := fun k hk => ext5 (fun _ h => yl_ge _ _ h) (fun _ h => yh_ge _ _ h)
    fun i hi => (e₂ k hk i hi).2
  refine WP.mono (mul_ok ⟨by rw [vec_gpr v₂, vec_gpr A.vec, hr8], fun k hk i hi => by
      rw [hH k hk]; exact A.hb k hk i hi, fun k hk i hi => by rw [hY k hk]; exact Y₁.hib k hk i hi⟩)
    fun s₃ M => ⟨vec_trans (vec_trans A.vec v₂) M.vec, M.hb, ?_⟩
  have e : ∀ k < 4, Limbs26.val (hv s₃ k) ≡ (Limbs26.val (hv s k) + mv (blk s k)) * R ^ (4 - k) [MOD P] := by
    intro k hk
    rw [val_congr (M.h k hk), hH k hk, hY k hk, blk_mv, ← A.h k hk]
    exact (Limbs26.mul_mod _ _).trans (Nat.ModEq.mul_left _ (Y₁.hi k hk))
  rw [group_bytes]
  exact Poly1305.horner_last (blk_length s 0) (blk_length s 1) (blk_length s 2) (blk_length s 3) hI.acc
    (e 0 (by decide)) (e 1 (by decide)) (e 2 (by decide)) (by simpa using e 3 (by decide))

end VG.Proof.Poly1305.X86_64.Avx2
