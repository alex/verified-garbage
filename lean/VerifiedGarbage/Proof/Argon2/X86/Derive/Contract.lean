import VerifiedGarbage.Proof.Argon2.X86.HPrime.Verified
import VerifiedGarbage.Proof.Argon2.X86.CompressVerified
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Impl.Argon2.X86.Derive

/-!
# Argon2 on x86 (32-bit): the contract of the derivation's proof

`deriveX86`: `vg_argon2`'s contract with its eighteen arguments only read
(`Spec.Argon2.deriveContract`, which lets the code write them, is reached by
narrowing), its precondition a structure (`DPre`). The derivation uses the
244 bytes of stack below its return address: 16 for the saved registers,
144 for the locals, and 84 for a call of `vg_argon2_hprime` (five arguments,
the return address and H′'s own 60 bytes).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

section
variable (s₀ : State)

abbrev kindV : BitVec 32 := arg s₀ 0
abbrev pwP : BitVec 32 := arg s₀ 1
abbrev pwL : Nat := (arg s₀ 2).toNat
abbrev saltP : BitVec 32 := arg s₀ 3
abbrev saltL : Nat := (arg s₀ 4).toNat
abbrev itersN : Nat := (arg s₀ 5).toNat
abbrev mcostN : Nat := (arg s₀ 6).toNat
abbrev lanesN : Nat := (arg s₀ 7).toNat
abbrev threadsN : Nat := (arg s₀ 8).toNat
abbrev secP : BitVec 32 := arg s₀ 9
abbrev secL : Nat := (arg s₀ 10).toNat
abbrev adP : BitVec 32 := arg s₀ 11
abbrev adL : Nat := (arg s₀ 12).toNat
abbrev memP : BitVec 32 := arg s₀ 13
abbrev blocksN : Nat := (arg s₀ 14).toNat
abbrev scrP : BitVec 32 := arg s₀ 15
abbrev outP : BitVec 32 := arg s₀ 16
abbrev outL : Nat := (arg s₀ 17).toNat
abbrev E0 : BitVec 32 := s₀.gpr .esp

/-- The parameters. -/
abbrev prm : Params := params (kindV s₀).toNat (itersN s₀) (mcostN s₀) (lanesN s₀) (outL s₀)

abbrev pwR : Region := ⟨(pwP s₀).setWidth 64, pwL s₀⟩
abbrev saltR : Region := ⟨(saltP s₀).setWidth 64, saltL s₀⟩
abbrev secR : Region := ⟨(secP s₀).setWidth 64, secL s₀⟩
abbrev adR : Region := ⟨(adP s₀).setWidth 64, adL s₀⟩
abbrev memR : Region := ⟨(memP s₀).setWidth 64, blocksN s₀ * 1024⟩
abbrev scrR : Region := ⟨(scrP s₀).setWidth 64, 16384⟩
abbrev outR : Region := ⟨(outP s₀).setWidth 64, outL s₀⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 72⟩
abbrev retR : Region := ⟨(E0 s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E0 s₀) 244

/-- The inputs, on entry. -/
abbrev pwB : List Byte := bytesAt s₀.mem (pwR s₀).base (pwL s₀)
abbrev saltB : List Byte := bytesAt s₀.mem (saltR s₀).base (saltL s₀)
abbrev secB : List Byte := bytesAt s₀.mem (secR s₀).base (secL s₀)
abbrev adB : List Byte := bytesAt s₀.mem (adR s₀).base (adL s₀)

end

/-- The facts of `deriveX86`'s precondition. -/
structure DPre (s₀ : State) : Prop where
  rd : s₀.rd = [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀]
  wr : s₀.wr = [memR s₀, scrR s₀, outR s₀]
  ro_w : ∀ r ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀], ∀ w ∈ [memR s₀, scrR s₀, outR s₀],
    r.Disjoint w
  mem_scr : (memR s₀).Disjoint (scrR s₀)
  mem_out : (memR s₀).Disjoint (outR s₀)
  scr_out : (scrR s₀).Disjoint (outR s₀)
  ret_w : ∀ w ∈ [memR s₀, scrR s₀, outR s₀], (retR s₀).Disjoint w
  stk_all : ∀ r ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀], (stkR s₀).Disjoint r
  pw_fits : (pwP s₀).toNat + pwL s₀ ≤ 2 ^ 32
  salt_fits : (saltP s₀).toNat + saltL s₀ ≤ 2 ^ 32
  sec_fits : (secP s₀).toNat + secL s₀ ≤ 2 ^ 32
  ad_fits : (adP s₀).toNat + adL s₀ ≤ 2 ^ 32
  mem_fits : (memP s₀).toNat + blocksN s₀ * 1024 ≤ 2 ^ 32
  scr_fits : (scrP s₀).toNat + 16384 ≤ 2 ^ 32
  out_fits : (outP s₀).toNat + outL s₀ ≤ 2 ^ 32
  esp_lo : 244 ≤ (E0 s₀).toNat
  esp_hi : (E0 s₀).toNat + 76 ≤ 2 ^ 32
  kind_le : (kindV s₀).toNat ≤ 2
  valid : valid (prm s₀) (pwL s₀) (saltL s₀) (secL s₀) (adL s₀)
  threads : 1 ≤ threadsN s₀ ∧ threadsN s₀ < 2 ^ 24
  blocks : blocksN s₀ = (prm s₀).blocks

/-- `vg_argon2`, with its arguments only read. -/
def deriveX86 : Contract X86.isa where
  pre := DPre
  post s s' := bytesAt s'.mem ((outP s).setWidth 64) (outL s) =
    derive (prm s) (pwB s) (saltB s) (secB s) (adB s)
  pub s₁ s₂ := (s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 18, arg s₁ i = arg s₂ i) ∧
    references (prm s₁) (pwB s₁) (saltB s₁) (secB s₁) (adB s₁) =
      references (prm s₂) (pwB s₂) (saltB s₂) (secB s₂) (adB s₂)

/-! ## Facts of the precondition -/

/-- Two disjoint, nonempty regions within `[0, N)` have at most `N` bytes in all. -/
theorem disjoint_total {a b : Region} (h : a.Disjoint b) {N : Nat}
    (ha : a.base.toNat + a.len ≤ N) (hb : b.base.toNat + b.len ≤ N) (pa : 0 < a.len) (pb : 0 < b.len) :
    a.len + b.len ≤ N := by
  have key : ∀ {a b : Region}, a.Disjoint b → a.base.toNat ≤ b.base.toNat → b.base.toNat + b.len ≤ N →
      0 < b.len → a.base.toNat + a.len ≤ b.base.toNat := fun {a b} h hle hb pb => by
    by_contra hlt
    refine h b.base ?_ ?_
    · simp only [Region.Contains]
      rw [BitVec.toNat_sub_of_le (by simpa [BitVec.le_def] using hle)]
      omega
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  rcases Nat.le_total a.base.toNat b.base.toNat with hle | hle
  · have := key h hle hb pb; omega
  · have := key h.symm hle ha pa; omega

namespace DPre
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem lanes_pos : 1 ≤ lanesN s₀ := hp.valid.1
theorem lanes_lt : lanesN s₀ < 2 ^ 24 := hp.valid.2.1
theorem passes_pos : 1 ≤ itersN s₀ := hp.valid.2.2.1
theorem memory_ge : 8 * lanesN s₀ ≤ mcostN s₀ := hp.valid.2.2.2.2.1
theorem tag_ge : 4 ≤ outL s₀ := hp.valid.2.2.2.2.2.2.1


theorem segLen_two : 2 ≤ (prm s₀).segmentLen :=
  Proof.Argon2.segmentLen_ge_two _ hp.lanes_pos hp.memory_ge

theorem segLen_eq : (prm s₀).segmentLen = mcostN s₀ / (4 * lanesN s₀) :=
  Proof.Argon2.segmentLen_eq _ hp.lanes_pos

theorem laneLen_eq : (prm s₀).laneLen = 4 * (prm s₀).segmentLen :=
  Proof.Argon2.laneLen_segments _ hp.lanes_pos

theorem blocks_eq : blocksN s₀ = lanesN s₀ * (prm s₀).laneLen := by
  rw [hp.blocks]; exact Proof.Argon2.blocks_lanes _ hp.lanes_pos

/-- The memory, with the scratch beside it, fits below 2³² with room to spare. -/
theorem blocks_lt : blocksN s₀ * 1024 + 16384 ≤ 2 ^ 32 := by
  have hm := hp.mem_fits
  have hs := hp.scr_fits
  rcases Nat.eq_zero_or_pos (blocksN s₀) with h0 | hpos
  · omega
  have := disjoint_total hp.mem_scr (N := 2 ^ 32)
    (by simp only [BitVec.toNat_setWidth, ]; omega)
    (by simp only [BitVec.toNat_setWidth, ]; omega)
    (by simp only; omega) (by simp only; omega)
  simpa using this

end DPre

end VG.Proof.Argon2.X86.Derive
