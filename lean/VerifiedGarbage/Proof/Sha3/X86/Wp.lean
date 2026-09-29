import VerifiedGarbage.Proof.Sha512.X86.Rounds
import VerifiedGarbage.Impl.Sha3.X86

/-!
# SHA-3 on x86 (32-bit): lanes as pairs of words

Untrusted: everything here is checked by Lean. The halves of the lanes
(`half`), their rotations as the code computes them (each half rotated, and
their top bits exchanged), and weakest-precondition rules for the macros of
`VG.Impl.Sha3.X86` that load, combine, rotate and store a lane in `(eax,
edx)`, each proved once for any registers and offsets, in
continuation-passing style. The halves and the 64-bit words in memory are
those of the SHA-512 proofs (`Proof/Sha512/X86/Steps.lean`).
-/

namespace VG.Proof.Sha3.X86

open VG VG.X86
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Sha3.X86 (sLo sHi ld2 xor2 st2 rot topMask)
open VG.Proof.Sha512.Word64 (lo hi lo_xor hi_xor lo_and hi_and lo_rotr hi_rotr)
open VG.Proof.Sha512.X86 (Only Pair rd64 write64 lo_rd64 hi_rd64 readSrc_mem wp_movS wp_xorS wp_andS
  wp_ror ea_of)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_store wp_mov)

abbrev Lane := Spec.Sha3.Lane

/-! ## Halves -/

/-- Half `h` of a lane: the low one for `h = 0`, else the high one. -/
def half (h : Nat) (v : Lane) : BitVec 32 := if h = 0 then lo v else hi v

theorem half_xor (h : Nat) (a b : Lane) : half h (a ^^^ b) = half h a ^^^ half h b := by
  unfold half; split
  · exact lo_xor a b
  · exact hi_xor a b

theorem half_and (h : Nat) (a b : Lane) : half h (a &&& b) = half h a &&& half h b := by
  unfold half; split
  · exact lo_and a b
  · exact hi_and a b

theorem half_ones (h : Nat) : half h (0xffffffffffffffff : Lane) = BitVec.allOnes 32 := by
  unfold half; split <;> rfl

theorem half_rd64 {h : Nat} (hh : h = 0 ∨ h = 4) (m : Mem) (b : BitVec 32) (o : Nat) :
    half h (rd64 m b o) = m.readW (addr b (o + h)) 32 := by
  rcases hh with rfl | rfl
  · exact lo_rd64 m b o
  · exact hi_rd64 m b o

theorem half_lo (v : Lane) : half 0 v = lo v := rfl

theorem half_hi (v : Lane) : half 4 v = hi v := rfl

/-! ## Rotations -/

/-- A rotation right by `0 < m < 32` of the halves `a` (low) and `b`: its low
half, as the code computes it. -/
theorem rot_half (a b : BitVec 32) {m : Nat} (h0 : 0 < m) (h : m < 32) :
    a >>> m ^^^ b <<< (32 - m) =
      a.rotateRight m ^^^ ((a.rotateRight m ^^^ b.rotateRight m) &&& topMask m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [topMask, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, Nat.mod_eq_of_lt h]
  by_cases hc : i < 32 - m
  · simp [hc, hi, show m + i < 32 by omega]
  · simp only [hc, hi, BitVec.getLsbD_of_ge a (m + i) (by omega), ite_false, decide_true,
      Bool.true_and, decide_false, Bool.not_false, show i - (32 - m) < 32 by omega]
    cases a.getLsbD (i - (32 - m)) <;> cases b.getLsbD (i - (32 - m)) <;> rfl

theorem lo_rotm (v : Lane) {m : Nat} (h0 : 0 < m) (h : m < 32) :
    lo (v.rotateRight m) = (lo v).rotateRight m ^^^
      (((lo v).rotateRight m ^^^ (hi v).rotateRight m) &&& topMask m) := by
  rw [lo_rotr _ h0 h, rot_half _ _ h0 h]

theorem hi_rotm (v : Lane) {m : Nat} (h0 : 0 < m) (h : m < 32) :
    hi (v.rotateRight m) = (hi v).rotateRight m ^^^
      (((lo v).rotateRight m ^^^ (hi v).rotateRight m) &&& topMask m) := by
  rw [hi_rotr _ h0 h, rot_half _ _ h0 h, BitVec.xor_comm ((hi v).rotateRight m) ((lo v).rotateRight m)]

theorem lo_rot32 (v : Lane) : lo (v.rotateRight 32) = hi v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [lo, hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight]
  simp [hi']

theorem hi_rot32 (v : Lane) : hi (v.rotateRight 32) = lo v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [lo, hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight]
  simp [hi', show 32 + i < 64 by omega, show ¬ 32 + i < 32 by omega]

theorem rotateRight_zero' (v : Lane) : v.rotateRight 0 = v := by
  ext i hi
  simp only [BitVec.getElem_rotateRight]
  split <;> (try congr 1) <;> omega

theorem rotateRight_add (v : Lane) {a b : Nat} (h : a + b < 64) :
    (v.rotateRight a).rotateRight b = v.rotateRight (a + b) := by
  ext i hi
  simp only [BitVec.getElem_rotateRight, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show a < 64 by omega),
    Nat.mod_eq_of_lt (show b < 64 by omega)]
  split <;> split <;> split <;> (try congr 1) <;> omega

/-- The lane `v`, its halves swapped if `sw`. -/
def swapIf (sw : Bool) (v : Lane) : Lane := if sw then v.rotateRight 32 else v

theorem swapIf_true (v : Lane) : swapIf true v = v.rotateRight 32 := rfl

theorem swapIf_false (v : Lane) : swapIf false v = v := rfl

theorem lo_swapIf (sw : Bool) (v : Lane) : lo (swapIf sw v) = half (sLo sw) v := by
  cases sw
  · rfl
  · exact lo_rot32 v

theorem hi_swapIf (sw : Bool) (v : Lane) : hi (swapIf sw v) = half (sHi sw) v := by
  cases sw
  · rfl
  · exact hi_rot32 v

theorem swapIf_xor (sw : Bool) (a b : Lane) : swapIf sw (a ^^^ b) = swapIf sw a ^^^ swapIf sw b := by
  cases sw
  · rfl
  · apply VG.Proof.Sha512.Word64.eq_of_lo_hi
    · simp only [swapIf, ite_true, lo_rot32, lo_xor, hi_xor]
    · simp only [swapIf, ite_true, hi_rot32, lo_xor, hi_xor]

theorem sLo_cases (sw : Bool) : sLo sw = 0 ∨ sLo sw = 4 := by cases sw <;> simp [sLo]

theorem sHi_cases (sw : Bool) : sHi sw = 0 ∨ sHi sw = 4 := by cases sw <;> simp [sHi]

/-! ## Single instructions -/

theorem Upd.trans {s₁ s₂ s₃ : State} {d : Reg} {v w : BitVec 32} (h₁ : Upd s₁ s₂ d v)
    (h₂ : Upd s₂ s₃ d w) : Upd s₁ s₃ d w :=
  ⟨h₂.gpr, fun r h => (h₂.other r h).trans (h₁.other r h), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- `mov d, [b + o]` -/
theorem wp_ldm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.mem.readW (addr B o) 32) → WP isa (.block rest) s' Q) :
    WP isa (.block (.mov d (.mem (at_ b o)) :: rest)) s Q :=
  wp_movS (readSrc_mem hb hin) k

/-- `xor d, [b + o]` -/
theorem wp_xorm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW (addr B o) 32) → WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .xor d (.mem (at_ b o)) :: rest)) s Q :=
  wp_xorS (readSrc_mem hb hin) k

/-- `and d, [b + o]` -/
theorem wp_andm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d &&& s.mem.readW (addr B o) 32) → WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .and d (.mem (at_ b o)) :: rest)) s Q :=
  wp_andS (readSrc_mem hb hin) k

/-- `mov [b + o], r` -/
theorem wp_stm {b r : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B) (hout : InRegions s.wr (addr B o) 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr B o) (s.gpr r)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.store (at_ b o) r :: rest)) s Q :=
  wp_store (ea_of hb o) hout k

end

/-! ## Lanes in `(eax, edx)` -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- Both words of the lane at `[B + o]` may be read. -/
def Rd2 (s : State) (B : BitVec 32) (o : Nat) : Prop :=
  ∀ h, h = 0 ∨ h = 4 → InRegions (s.rd ++ s.wr) (addr B (o + h)) 4

theorem wp_ld2 {sw : Bool} {b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B) (hbe : b ≠ .eax)
    (hin : Rd2 s B o)
    (k : ∀ s', Only [.eax, .edx] s s' → Pair s' .eax .edx (swapIf sw (rd64 s.mem B o)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (ld2 sw b o ++ rest)) s Q := by
  simp only [ld2, List.cons_append, List.nil_append]
  refine wp_ldm hb (hin _ (sLo_cases sw)) fun s₁ u₁ => ?_
  refine wp_ldm (by rw [u₁.other _ hbe, hb]) (by rw [u₁.rd, u₁.wr]; exact hin _ (sHi_cases sw))
    fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other _ (by decide), u₁.gpr, lo_swapIf, half_rd64 (sLo_cases sw)]
  · rw [u₂.gpr, u₁.mem, hi_swapIf, half_rd64 (sHi_cases sw)]

theorem wp_xor2 {sw : Bool} {b : Reg} {B : BitVec 32} {o : Nat} {v : Lane} (hb : s.gpr b = B)
    (hbe : b ≠ .eax) (hin : Rd2 s B o) (hp : Pair s .eax .edx v)
    (k : ∀ s', Only [.eax, .edx] s s' → Pair s' .eax .edx (v ^^^ swapIf sw (rd64 s.mem B o)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (xor2 sw b o ++ rest)) s Q := by
  simp only [xor2, List.cons_append, List.nil_append]
  refine wp_xorm hb (hin _ (sLo_cases sw)) fun s₁ u₁ => ?_
  refine wp_xorm (by rw [u₁.other _ hbe, hb]) (by rw [u₁.rd, u₁.wr]; exact hin _ (sHi_cases sw))
    fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other _ (by decide), u₁.gpr, lo_xor, lo_swapIf, half_rd64 (sLo_cases sw), hp.1]
  · rw [u₂.gpr, u₁.mem, u₁.other _ (by decide), hi_xor, hi_swapIf, half_rd64 (sHi_cases sw), hp.2]

theorem wp_rot {m : Nat} (hm : m < 32) {v : Lane} (hp : Pair s .eax .edx v)
    (k : ∀ s', Only [.eax, .edx, .ecx] s s' → Pair s' .eax .edx (v.rotateRight m) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (rot m ++ rest)) s Q := by
  unfold rot
  split
  · rename_i h0
    subst h0
    simp only [List.nil_append]
    exact k s (Only.refl _ _) (by rw [rotateRight_zero']; exact hp)
  · rename_i h0
    simp only [List.cons_append, List.nil_append]
    refine wp_ror ⟨by omega, by omega⟩ fun s₁ u₁ => wp_ror ⟨by omega, by omega⟩ fun s₂ u₂ =>
      wp_mov fun s₃ u₃ => wp_xorS rfl fun s₄ u₄ => wp_andS rfl fun s₅ u₅ =>
      wp_xorS rfl fun s₆ u₆ => wp_xorS rfl fun s₇ u₇ => k s₇ ?_ ⟨?_, ?_⟩
    · exact ((((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
        (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans (Only.of_upd u₆)).trans (Only.of_upd u₇)
        |>.mono (by simp)
    all_goals
      have hA : s₂.gpr .eax = (lo v).rotateRight m := by
        rw [u₂.other .eax (by decide), u₁.gpr, hp.1]
      have hB : s₂.gpr .edx = (hi v).rotateRight m := by
        rw [u₂.gpr, u₁.other .edx (by decide), hp.2]
      have e5a : s₅.gpr .eax = (lo v).rotateRight m := by
        rw [u₅.other .eax (by decide), u₄.other .eax (by decide), u₃.other .eax (by decide), hA]
      have e5c : s₅.gpr .ecx = ((lo v).rotateRight m ^^^ (hi v).rotateRight m) &&& topMask m := by
        rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other .edx (by decide), hA, hB]
    · rw [u₇.other .eax (by decide), u₆.gpr, e5a, e5c, lo_rotm _ (by omega) hm]
    · rw [u₇.gpr, u₆.other .edx (by decide), u₆.other .ecx (by decide), e5c, u₅.other .edx (by decide),
        u₄.other .edx (by decide), u₃.other .edx (by decide), hB, hi_rotm _ (by omega) hm]

/-- Both words of the lane at `[B + o]` may be written. -/
def Wr2 (s : State) (B : BitVec 32) (o : Nat) : Prop :=
  InRegions s.wr (addr B o) 4 ∧ InRegions s.wr (addr B (o + 4)) 4

theorem wp_st2 {b : Reg} {B : BitVec 32} {o : Nat} {v : Lane} (hb : s.gpr b = B)
    (hout : Wr2 s B o) (hp : Pair s .eax .edx v)
    (k : ∀ s', Mupd s s' (write64 s.mem B o v) → WP isa (.block rest) s' Q) :
    WP isa (.block (st2 b o ++ rest)) s Q := by
  simp only [st2, List.cons_append, List.nil_append]
  refine wp_stm hb hout.1 fun s₁ u₁ => ?_
  refine wp_stm (by rw [u₁.gpr, hb]) (by rw [u₁.wr]; exact hout.2)
    fun s₂ u₂ => k s₂ ⟨u₂.gpr.trans u₁.gpr, ?_, u₂.rd.trans u₁.rd, u₂.wr.trans u₁.wr⟩
  rw [u₂.mem, u₁.mem, u₁.gpr, hp.1, hp.2]; rfl

end

end VG.Proof.Sha3.X86
