import VerifiedGarbage.Proof.MlDsa.Arm.Sample.BallLoop

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_sample_in_ball`, correctness

Untrusted: everything here is checked by Lean. The function runs in pieces:
the prologue (`J0`), the sponge, whose output is `H(c̃, 272)` (`J6`), the
zeroing of `c` (`ZDone`), the setup of the loop, which loads the sign bits
(`setup_ok`, with `readW_pair`: the two words are the first 8 bytes of
output as a little-endian number), and the 264 iterations of the loop
(`BAt`, `body_ok`), after which `c` and `i` are what `ballFold` computes.
-/

namespace VG.Proof.MlDsa.Arm.Sample.Ball

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H IPoly n ofInt coeffAt PolyIs toRq)
open VG.Spec.Sha3 (bytesAt)

/-! ## The sign bits -/

theorem readW32_getLsbD (m : Mem) (a : Addr) {k : Nat} (hk : k < 32) :
    (m.readW a 32).getLsbD k = (m (a + BitVec.ofNat 64 (k / 8))).getLsbD (k % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 4) (j := k / 8) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, show k % 8 < 8 by omega, decide_true, Bool.true_and, hk]
  congr 1; omega

/-- The two words at `a`, as a number: the first 8 bytes there. -/
theorem readW_pair (m : Mem) (a : Addr) (L : List Byte) (h : ∀ k < 8, m (a + BitVec.ofNat 64 k) = L.getD k 0) :
    (m.readW a 32).toNat + 2 ^ 32 * (m.readW (a + BitVec.ofNat 64 4) 32).toNat = leNat (L.take 8) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ (BitVec.isLt _), testBit_leNat]
  split
  · rename_i hk
    rw [BitVec.testBit_toNat, readW32_getLsbD _ _ hk, h _ (by omega), List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
  · rename_i hk
    rw [BitVec.testBit_toNat]
    by_cases h64 : k < 64
    · rw [readW32_getLsbD _ _ (by omega), add_ofNat_add, show 4 + (k - 32) / 8 = k / 8 by omega,
        show (k - 32) % 8 = k % 8 by omega, h _ (by omega), List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
    · rw [BitVec.getLsbD_of_ge _ _ (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [List.length_take]; omega)]
      simp

/-! ## The setup of the loop -/

theorem setup1_ok (s : State) {A C : Addr} (hA : State.addr (s.gpr .r6 + BitVec.ofNat 32 840) = A)
    (hC : State.addr (s.gpr .r6 + BitVec.ofNat 32 844) = C) (hrA : InRegions (s.rd ++ s.wr) A 4)
    (hrC : InRegions (s.rd ++ s.wr) C 4) :
    WP isa (.block (bSetup ++ [.mov .r3 (.imm 264)])) s fun s' =>
      s'.gpr .r1 = s.mem.readW A 32 ∧ s'.gpr .r4 = s.mem.readW C 32 ∧
        s'.gpr .r2 = BitVec.ofNat 32 256 - s.gpr .r7 ∧ s'.gpr .r0 = s.gpr .r6 + BitVec.ofNat 32 848 ∧
        s'.gpr .r3 = BitVec.ofNat 32 264 ∧ s'.gpr .r5 = s.gpr .r5 ∧ s'.gpr .r6 = s.gpr .r6 ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [bSetup, hA, hC, hrA, hrC, and_self, and_true, true_and]
  exact ⟨rfl, rfl⟩

section
variable {σ : State} (hp : SpOk (spOf σ) σ) (hτ : tau σ ≤ 256)
include hp hτ

theorem setup_ok {s : State} (h : ZDone σ s) :
    WP isa (.block (bSetup ++ [.mov .r3 (.imm 264)])) s (BAt σ 0) := by
  have e6 := h.env.r6
  have hA : State.addr (s.gpr .r6 + BitVec.ofNat 32 840) = (spOf σ).at' 840 := by rw [e6]; exact at_eq hp (by omega)
  have hC : State.addr (s.gpr .r6 + BitVec.ofNat 32 844) = (spOf σ).at' 840 + BitVec.ofNat 64 4 := by
    rw [e6, at_eq hp (by omega), add_ofNat_add]
  have hC' : InRegions (s.rd ++ s.wr) ((spOf σ).at' 840 + BitVec.ofNat 64 4) 4 := by
    rw [add_ofNat_add]; exact inScrRd hp h.env (by omega)
  refine WP.mono (setup1_ok s hA hC (inScrRd hp h.env (by omega)) hC')
    fun s' ⟨g1, g4, g2, g0, g3, g5, g6, m, rd, wr, sp⟩ => ?_
  have hSt : St σ 0 = (Vector.replicate n 0, i0 σ) := rfl
  refine ⟨h.env.same m g5 g6 rd wr sp, by rw [m]; exact h.out, by rw [g0, e6], ?_, ?_,
    by rw [g3], by rw [m, hSt]; exact h.st⟩
  · rw [g2, h.r7, hSt]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, toNat_ofNat32 (by omega), toNat_ofNat32 (by simp only [i0]; omega)]
    have := (σ.gpr .r2).isLt
    simp only [i0, tau] at hτ ⊢
    omega
  · show _ = _
    rw [g1, g4, hSt, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    exact readW_pair _ _ _ fun k hk => by
      have := congrArg (fun L => L.getD k 0) h.out
      rw [MlKem.bytesAt_getD _ _ (by omega)] at this
      exact this

/-- The loop, from the zeroed polynomial. -/
theorem loop_ok {s : State} (h : ZDone σ s) : WP isa bLoop s (BAt σ 264) :=
  WP.seq (WP.mono (setup_ok hp hτ h) fun _ h0 =>
    wp_loop_ne (BAt σ) (N := 264) (by decide) (fun t ht s h => body_ok hp hτ ht h) (fun _ h => h) h0)

end

/-! ## The end -/

theorem St_all (σ : State) : St σ 264 = ballFold (tau σ) (X σ) := by
  simp only [St, ballFold, i0]; rw [List.take_of_length_le (by rw [List.length_drop, X_length])]

theorem end_ok {σ : State} (hp : SpOk (spOf σ) σ) {s : State} (h : BAt σ 264 s) :
    WP isa (.block (retJ ++ epi)) s fun s' =>
      s'.gpr .r0 = (if (ballFold (tau σ) (X σ)).2 = 256 then 1 else 0) ∧
      ((ballFold (tau σ) (X σ)).2 = 256 →
        PolyIs s'.mem (State.addr (σ.gpr .r3)) (toRq (ballFold (tau σ) (X σ)).1)) ∧
      abiPreserved σ s' :=
  WP.mono (retEpi_ok hp h.env h.r2 (St_le _ _)) fun s' ⟨h0, hm, ha⟩ => ⟨by rw [h0, St_all], fun _ => by
    rw [hm]
    have hst := h.st
    rw [St_all] at hst
    refine polyIs_of_coeffAt fun i hi => ?_
    rw [hst i hi, getElem!_pos _ i hi, getElem!_pos _ i hi]
    simp only [toRq, Vector.getElem_map], ha⟩

/-- The function, from an entry state whose regions are those of a call. -/
theorem correct {σ : State} (hp : Pre σ) : WP isa Impl.MlDsa.Arm.Sample.sampleInBall σ fun s' =>
    s'.gpr .r0 = (if (ballFold (tau σ) (X σ)).2 = 256 then 1 else 0) ∧
      ((ballFold (tau σ) (X σ)).2 = 256 →
        PolyIs s'.mem (State.addr (σ.gpr .r3)) (toRq (ballFold (tau σ) (X σ)).1)) ∧
      abiPreserved σ s' := by
  have hτ : tau σ ≤ 256 := by have := hp.tau_le; omega
  exact WP.seq (WP.mono (pro_ball hp.ok rfl (by simp) rfl rfl rfl hp.arg) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok hp.ok (rate := 136) (outlen := 272) (by decide) (by decide) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (zero_ok hp.ok h2) fun _ h3 => WP.seq (WP.mono (loop_ok hp.ok hτ h3)
        fun _ h4 => end_ok hp.ok h4))))

end VG.Proof.MlDsa.Arm.Sample.Ball
