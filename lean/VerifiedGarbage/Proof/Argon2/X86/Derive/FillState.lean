import VerifiedGarbage.Proof.Argon2.X86.Derive.FillSteps
import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.FillPositions

/-!
# Argon2 on x86 (32-bit): the state of the filling loops

`FS s₀ pass slice lane index ctr st`: the body at a position of the filling
loops (`Pos`), the memory matrix representing `st`'s, and the address block
cached in `scratch[6144, 7168)` that of the counter in the locals, if it is
not zero (`CacheOk`). `addressMode_ok`: `addressMode` sets ZF for
data-dependent addressing.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_sbb_self wp_and wp_or
  wp_andi)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState addressBlock independent)
open VG.Proof.Argon2.X86 (blk)
open VG.Proof.Sha512.X86 (rd64)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff)

/-- The address block cached at `scratch + 6144`, for the counter in the locals. -/
def CacheOk (s₀ : State) (pass lane slice ctr : Nat) (s : State) : Prop :=
  ctr < 2 ^ 32 ∧ lw s₀ s counterOff = BitVec.ofNat 32 ctr ∧
    (ctr = 0 ∨ 1 ≤ ctr ∧ blk s.mem (scrP s₀) 6144 = addressBlock (prm s₀) pass lane slice ctr)

/-- The counter after a block: the index's group, for data-independent addressing. -/
def ctrNext (p : Spec.Argon2.Params) (pass slice index ctr : Nat) : Nat :=
  if independent p pass slice then index / 128 + 1 else ctr

/-- The filling loops' state at a position, the memory matrix holding `st`'s. -/
structure FS (s₀ : State) (pass slice lane index ctr : Nat) (st : FillState) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  pos : Pos s₀ s pass slice lane index
  cache : CacheOk s₀ pass lane slice ctr s
  mem : Represents s.mem (memB s₀) (prm s₀).blocks st.memory

theorem Divide.Keep.of_fupd {s t : State} (f : Fupd s t) : Divide.Keep s t :=
  ⟨fun _ _ _ _ => by rw [f.gpr], f.mem, f.rd, f.wr⟩

theorem Represents.keep {m m' : Mem} {base : Addr} {n : Nat} {b : Array Block}
    (h : Represents m base n b) (hk : ∀ k < n, blockAt m' (matrixCell base k) = blockAt m (matrixCell base k)) :
    Represents m' base n b :=
  ⟨h.size, fun k hk' => (hk k hk').trans (h.block k hk')⟩

/-- The block at `B + o`, from `B + o` as its base. -/
theorem blk_shift (m : Mem) (B : BitVec 32) (o : Nat) : blk m (B + BitVec.ofNat 32 o) 0 = blk m B o := by
  apply Vector.ext
  intro j hj
  simp only [blk, Vector.getElem_ofFn, rd64, addr, Nat.zero_add, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    Nat.add_assoc]

/-- The cells of the matrix, as `blk`. -/
theorem cell_blk {s₀ : State} (hp : DPre s₀) (m : Mem) {k : Nat} (hk : k < blocksN s₀) :
    blockAt m (matrixCell (memB s₀) k) = blk m (memP s₀) (k * 1024) := by
  have := hp.mem_fits
  have : k * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
  rw [← cell_addr hp hk, Proof.Argon2.X86.blockAt_eq (by rw [add_nat (by omega)]; omega), blk_shift]

/-- The first word of a block. -/
theorem blk_zero (m : Mem) (B : BitVec 32) (o : Nat) :
    (blk m B o)[0] = m.readW (addr B (o + 4)) 32 ++ m.readW (addr B o) 32 := by
  simp only [blk, Vector.getElem_ofFn, rd64, Nat.mul_zero, Nat.add_zero]

/-- Word `j` of a block. -/
theorem blk_get (m : Mem) (B : BitVec 32) (o j : Nat) (hj : j < 128) :
    (blk m B o)[j] = m.readW (addr B (o + 8 * j + 4)) 32 ++ m.readW (addr B (o + 8 * j)) 32 := by
  simp only [blk, Vector.getElem_ofFn, rd64]

/-! ## The addressing mode -/

theorem independent_eq {s₀ : State} (hk : (kindV s₀).toNat ≤ 2) (pass slice : Nat) :
    independent (prm s₀) pass slice = (decide ((kindV s₀).toNat = 1) ||
      (decide ((kindV s₀).toNat = 2) && decide (pass = 0) && decide (slice < 2))) := by
  have hv : (prm s₀).variant = (if (kindV s₀).toNat = 0 then .d else if (kindV s₀).toNat = 1 then .i else .id) :=
    rfl
  have e1 : (Spec.Argon2.Variant.d == .i) = false := rfl
  have e2 : (Spec.Argon2.Variant.d == .id) = false := rfl
  have e3 : (Spec.Argon2.Variant.i == .i) = true := rfl
  have e3' : (Spec.Argon2.Variant.i == .id) = false := rfl
  have e4 : (Spec.Argon2.Variant.id == .i) = false := rfl
  have e5 : (Spec.Argon2.Variant.id == .id) = true := rfl
  rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with h | h | h
  · rw [independent, hv, ite_eq_left h, e1, e2, h]; simp
  · rw [independent, hv, ite_eq_right (by omega), ite_eq_left h, e3, e3', h]; simp
  · rw [independent, hv, ite_eq_right (by omega), ite_eq_right (by omega), e4, e5, h]; simp
    cases pass <;> rfl

theorem mode_bits (a b c d : Bool) :
    ((((if a then BitVec.allOnes 32 else 0) ||| ((if b then BitVec.allOnes 32 else 0) &&&
      (if c then BitVec.allOnes 32 else 0) &&& (if d then BitVec.allOnes 32 else 0))) &&& 1) - 0 == 0) =
      !(a || (b && c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `addressMode`: ZF for data-dependent addressing. -/
theorem addressMode_ok {s : State} (h : Inv s₀ s) {pass slice lane index : Nat}
    (ps : Pos s₀ s pass slice lane index) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block Impl.Argon2.X86.Derive.addressMode) s fun t =>
      t.zf = some (!independent (prm s₀) pass slice) ∧ Divide.Keep s t := by
  have hk := hp.kind_le
  unfold Impl.Argon2.X86.Derive.addressMode
  refine wp_ldarg hp h (i := 0) (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_xori fun s₃ u₃ =>
    wp_cmpi fun s₄ f₄ c₄ _ => wp_sbb_self c₄ fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_xori fun s₇ u₇ =>
    wp_cmpi fun s₈ f₈ c₈ _ => wp_sbb_self c₈ fun s₉ u₉ => ?_
  have K₉ : Divide.Keep s s₉ :=
    ((((((((Divide.Keep.of_upd u₁ (by simp)).trans (Divide.Keep.of_upd u₂ (by simp))).trans
      (Divide.Keep.of_upd u₃ (by simp))).trans (Divide.Keep.of_fupd f₄)).trans (Divide.Keep.of_upd u₅ (by simp))).trans
      (Divide.Keep.of_upd u₆ (by simp))).trans (Divide.Keep.of_upd u₇ (by simp))).trans
      (Divide.Keep.of_fupd f₈)).trans (Divide.Keep.of_upd u₉ (by simp))
  refine wp_ldloc hp (h.keep K₉) (d := passOff) (by decide) fun s₁₀ u₁₀ => wp_cmpi fun s₁₁ f₁₁ c₁₁ _ =>
    wp_sbb_self c₁₁ fun s₁₂ u₁₂ => wp_and fun s₁₃ u₁₃ => ?_
  have K₁₃ : Divide.Keep s s₁₃ :=
    (((K₉.trans (Divide.Keep.of_upd u₁₀ (by simp))).trans (Divide.Keep.of_fupd f₁₁)).trans
      (Divide.Keep.of_upd u₁₂ (by simp))).trans (Divide.Keep.of_upd u₁₃ (by simp))
  refine wp_ldloc hp (h.keep K₁₃) (d := sliceOff) (by decide) fun s₁₄ u₁₄ => wp_cmpi fun s₁₅ f₁₅ c₁₅ _ =>
    wp_sbb_self c₁₅ fun s₁₆ u₁₆ => wp_and fun s₁₇ u₁₇ => wp_or fun s₁₈ u₁₈ => wp_andi fun s₁₉ u₁₉ =>
    wp_cmpi fun t f _ z => WP.block_nil ⟨?_, ?_⟩
  · -- The masks.
    have e₅ : s₅.gpr .ecx = if decide ((kindV s₀ ^^^ 1).toNat < 1) then BitVec.allOnes 32 else 0 := by
      rw [u₅.gpr]; congr 2
      rw [u₃.gpr, u₂.gpr, u₁.gpr]; rfl
    have e₉ : s₉.gpr .edx = if decide ((kindV s₀ ^^^ 2).toNat < 1) then BitVec.allOnes 32 else 0 := by
      rw [u₉.gpr]; congr 2
      rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.gpr]; rfl
    have p₁₀ : (s₁₀.gpr .eax).toNat = pass := by
      rw [u₁₀.gpr, lw_mem K₉.mem, ps.pass, Wp.toNat_ofNat_lt hpass]
    have e₁₃ : s₁₃.gpr .edx = s₉.gpr .edx &&& if decide (pass < 1) then BitVec.allOnes 32 else 0 := by
      rw [u₁₃.gpr, u₁₂.other _ (by decide), f₁₁.gpr, u₁₀.other _ (by decide), u₁₂.gpr]
      congr 3
      rw [p₁₀]; rfl
    have p₁₄ : (s₁₄.gpr .eax).toNat = slice := by
      rw [u₁₄.gpr, lw_mem K₁₃.mem, ps.slice, Wp.toNat_ofNat_lt (by omega)]
    have e₁₇ : s₁₇.gpr .edx = s₁₃.gpr .edx &&& if decide (slice < 2) then BitVec.allOnes 32 else 0 := by
      rw [u₁₇.gpr, u₁₆.other _ (by decide), f₁₅.gpr, u₁₄.other _ (by decide), u₁₆.gpr]
      congr 3
      rw [p₁₄]; rfl
    have e₁₈ : s₁₈.gpr .ecx = s₅.gpr .ecx ||| s₁₇.gpr .edx := by
      rw [u₁₈.gpr, u₁₇.other _ (by decide), u₁₆.other _ (by decide), f₁₅.gpr, u₁₄.other _ (by decide),
        u₁₃.other _ (by decide), u₁₂.other _ (by decide), f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
        f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide)]
    rw [z, u₁₉.gpr, e₁₈, e₁₇, e₁₃, e₉, e₅, independent_eq hk]
    have k3 : decide ((kindV s₀ ^^^ 1).toNat < 1) = decide ((kindV s₀).toNat = 1) ∧
        decide ((kindV s₀ ^^^ 2).toNat < 1) = decide ((kindV s₀).toNat = 2) := by
      rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with e | e | e <;>
        · rw [show kindV s₀ = BitVec.ofNat 32 (kindV s₀).toNat by simp, e]; decide
    rw [k3.1, k3.2, show decide (pass < 1) = decide (pass = 0) by simp only [Nat.lt_one_iff],
      mode_bits]
  · exact (((((((K₁₃.trans (Divide.Keep.of_upd u₁₄ (by simp))).trans (Divide.Keep.of_fupd f₁₅)).trans
      (Divide.Keep.of_upd u₁₆ (by simp))).trans (Divide.Keep.of_upd u₁₇ (by simp))).trans
      (Divide.Keep.of_upd u₁₈ (by simp))).trans (Divide.Keep.of_upd u₁₉ (by simp))).trans (Divide.Keep.of_fupd f))

end

end VG.Proof.Argon2.X86.Derive
