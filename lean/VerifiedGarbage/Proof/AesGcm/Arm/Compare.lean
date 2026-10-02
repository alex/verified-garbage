import VerifiedGarbage.Proof.AesGcm.Arm.Entry

/-!
# AES-GCM on ARMv7: checking a received tag

Untrusted: everything here is checked by Lean. `tagLenOk` sets `Z` iff the
tag length in `r6` is not one §5.2.1.2 allows (`tagLenOk_ok`); `recv` and
`cmp o` copy the received tag and the computed one, `r6` bytes of each,
padded with zeros, to `W + 256` and `W + 240` (`recv_ok`, `cmpCopy_ok`), and
`cmpTail` sets `r0` to 1 if they are equal and 0 if not, without a branch
(`cmpTail_ok`); `mask` keeps the tag at `W` if `r0` is 1 and zeroes it if 0
(`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le4 store4)

theorem shr31 (y : BitVec 32) : (y >>> 31).toNat = if y.msb then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  have := y.isLt
  by_cases h : 2 ^ (32 - 1) ≤ y.toNat
  · rw [decide_eq_true h]; simp only [ite_true]; simp only [Nat.reduceSub] at h; omega
  · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ite_false]; simp only [Nat.reduceSub] at h; omega

theorem msb_or_neg (x : BitVec 32) : (x ||| (0 - x)) >>> 31 = if x = 0 then 0 else 1 := by
  apply BitVec.eq_of_toNat_eq
  have z0 : (0 : BitVec 32).toNat = 0 := rfl
  rw [shr31, BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide (x := 0 - x), BitVec.toNat_sub, z0,
    Nat.add_zero]
  have := x.isLt
  by_cases h : x = 0
  · subst h; decide
  · have hx : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have : 2 ^ (32 - 1) ≤ x.toNat ∨ 2 ^ (32 - 1) ≤ (2 ^ 32 - x.toNat) % 2 ^ 32 := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp only [h, ite_false, Bool.or_eq_true, decide_eq_true_eq]
    simp only [this, ite_true]; rfl
theorem le4_inj {x y : BitVec 32} (h : le4 x = le4 y) : x = y := by
  have e : ∀ k < 4, x.extractLsb' (8 * k) 8 = y.extractLsb' (8 * k) 8 := fun k hk => by
    have := congrArg (fun l => l.getD k 0) h
    simpa only [Cmac.getD_le4 _ hk] using this
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have := congrArg (fun v => v.getLsbD (j % 8)) (e (j / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show j % 8 < 8 from Nat.mod_lt _ (by decide), decide_true,
    Bool.true_and] at this
  rwa [show 8 * (j / 8) + j % 8 = j by omega] at this

/-- `chk k`: `r0 := 1` if `r6 = k`. -/
theorem chk_ok (k : Nat) (hk : k < 2 ^ 32) (he : encodable (BitVec.ofNat 32 k) = true) {s : State} {tl : Nat}
    (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (htl : tl < 2 ^ 32) {p : Bool}
    (h0 : s.gpr .r0 = if p then 1 else 0) :
    WP isa (chk k) s fun s' => s'.gpr .r0 = (if (tl == k || p) then 1 else 0) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨s₁, run₁, hz, hg, hm, hrd, hwr, hsp⟩ := cmpk_ok s .r6 h6 htl hk he
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite _ (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have e : tl = k := by simpa using ht
    refine WP.of_runBlock ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg, e]
    · intro r hr; simp [gpr_setReg, hr, hg]
    · exact ⟨hm, hrd, hwr, hsp⟩
  · have e : tl ≠ k := by simpa using hf
    refine WP.block_nil ⟨?_, fun r _ => by rw [hg], ⟨hm, hrd, hwr, hsp⟩⟩
    rw [hg, h0]; simp [e]

theorem tagLenOk_eq (tl : Nat) :
    (tl == 16 || (tl == 15 || (tl == 14 || (tl == 13 || (tl == 12 || (tl == 8 || (tl == 4 || false))))))) =
      Spec.Gcm.tagLenOk tl := by
  simp only [Spec.Gcm.tagLenOk]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, Bool.or_false]
  omega

/-- `tagLenOk`: `Z` clear iff the tag length is allowed. -/
theorem tagLenOk_ok {s : State} {tl : Nat} (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (htl : tl < 2 ^ 32) :
    WP isa tagLenOk s fun s' => s'.z = !Spec.Gcm.tagLenOk tl ∧ (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨s₀, run₀, h0₀, hg₀, hk₀⟩ : ∃ s₀, runBlock isa [.mov .r0 (imm 0)] s = some s₀ ∧
      s₀.gpr .r0 = (if false then 1 else 0) ∧ (∀ r, r ≠ .r0 → s₀.gpr r = s.gpr r) ∧ Keeps s s₀ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  have g6 : ∀ {s' : State}, (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) → s'.gpr .r6 = BitVec.ofNat 32 tl :=
    fun hg => by rw [hg _ (by decide), h6]
  refine WP.seq (WP.mono (chk_ok 4 (by decide) (by decide) (g6 hg₀) htl h0₀) fun s₁ ⟨h0₁, hg₁, hk₁⟩ => ?_)
  have hg₁' : ∀ r, r ≠ .r0 → s₁.gpr r = s.gpr r := fun r hr => (hg₁ r hr).trans (hg₀ r hr)
  refine WP.seq (WP.mono (chk_ok 8 (by decide) (by decide) (g6 hg₁') htl h0₁) fun s₂ ⟨h0₂, hg₂, hk₂⟩ => ?_)
  have hg₂' : ∀ r, r ≠ .r0 → s₂.gpr r = s.gpr r := fun r hr => (hg₂ r hr).trans (hg₁' r hr)
  refine WP.seq (WP.mono (chk_ok 12 (by decide) (by decide) (g6 hg₂') htl h0₂) fun s₃ ⟨h0₃, hg₃, hk₃⟩ => ?_)
  have hg₃' : ∀ r, r ≠ .r0 → s₃.gpr r = s.gpr r := fun r hr => (hg₃ r hr).trans (hg₂' r hr)
  refine WP.seq (WP.mono (chk_ok 13 (by decide) (by decide) (g6 hg₃') htl h0₃) fun s₄ ⟨h0₄, hg₄, hk₄⟩ => ?_)
  have hg₄' : ∀ r, r ≠ .r0 → s₄.gpr r = s.gpr r := fun r hr => (hg₄ r hr).trans (hg₃' r hr)
  refine WP.seq (WP.mono (chk_ok 14 (by decide) (by decide) (g6 hg₄') htl h0₄) fun s₅ ⟨h0₅, hg₅, hk₅⟩ => ?_)
  have hg₅' : ∀ r, r ≠ .r0 → s₅.gpr r = s.gpr r := fun r hr => (hg₅ r hr).trans (hg₄' r hr)
  refine WP.seq (WP.mono (chk_ok 15 (by decide) (by decide) (g6 hg₅') htl h0₅) fun s₆ ⟨h0₆, hg₆, hk₆⟩ => ?_)
  have hg₆' : ∀ r, r ≠ .r0 → s₆.gpr r = s.gpr r := fun r hr => (hg₆ r hr).trans (hg₅' r hr)
  refine WP.seq (WP.mono (chk_ok 16 (by decide) (by decide) (g6 hg₆') htl h0₆) fun s₇ ⟨h0₇, hg₇, hk₇⟩ => ?_)
  have hg₇' : ∀ r, r ≠ .r0 → s₇.gpr r = s.gpr r := fun r hr => (hg₇ r hr).trans (hg₆' r hr)
  have hk : Keeps s s₇ := hk₀.trans (hk₁.trans (hk₂.trans (hk₃.trans (hk₄.trans (hk₅.trans (hk₆.trans hk₇))))))
  rw [tagLenOk_eq] at h0₇
  refine WP.of_runBlock ⟨_, by arun [], ?_, ?_, ?_⟩
  · simp only [z_subFlags, h0₇]
    cases Spec.Gcm.tagLenOk tl <;> rfl
  · intro r hr; simp only [gpr_subFlags]; exact hg₇' r hr
  · exact ⟨hk.mem, hk.rd, hk.wr, hk.sp⟩

end VG.Proof.AesGcm.Arm
