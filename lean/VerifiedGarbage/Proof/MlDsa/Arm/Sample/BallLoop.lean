import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
import VerifiedGarbage.Impl.MlDsa.Arm.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask

/-!
# ML-DSA on 32-bit ARM: the loops of `vg_mldsa_sample_in_ball`

Untrusted: everything here is checked by Lean. A call is described by
`spOf σ` (`c̃`, its length, `scratch`, `c` and `τ`), and the XOF output is
`X σ`, `H(c̃, 272)`. The polynomial `c` is kept in memory as the words that
represent its coefficients modulo `q` (`CStored`); the first loop zeroes it
(`zero_ok`). Iteration `t` of the second starts from `BAt σ t`: with the
polynomial and `i` (in `r2`) that `bFold` computes from the first `t` bytes
after the sign bits, and the sign bits not yet used in `r1` (low word) and
`r4` (high word), whose value `r1 + 2³² r4` is that of the first 8 bytes
shifted right once per coefficient set (`Sg`). The pieces of an iteration
are `pieceA` (`i ≥ 256`?), `tryA` (the byte `j`, and `j ≤ i`?), `setOk`
(`c[i] ← c[j]`, `c[j] ← ±1`) and `pieceC` (the step).
-/

namespace VG.Proof.MlDsa.Arm.Sample.Ball

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H IPoly n ofInt coeffAt)
open VG.Spec.Sha3 (bytesAt)

/-- The call, from the entry state: `ctilde = r0`, `len = r1`, `tau = r2`,
`c = r3` and `scratch` on the stack. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r0, (σ.gpr .r1).toNat, stackArg σ 0, σ.gpr .r3, σ.gpr .r2⟩

/-- `τ`. -/
abbrev tau (σ : State) : Nat := (σ.gpr .r2).toNat

/-- `c̃`. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r0)) (σ.gpr .r1).toNat

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H (B σ) 272

/-- The first `i`. -/
abbrev i0 (σ : State) : Nat := 256 - tau σ

/-- The sign bits, as a number. -/
abbrev Wn (σ : State) : Nat := leNat ((X σ).take 8)

/-- The polynomial and `i` after `t` iterations. -/
abbrev St (σ : State) (t : Nat) : IPoly × Nat :=
  bFold (tau σ) (signs (X σ)) (Vector.replicate n 0, i0 σ) (((X σ).drop 8).take t)

/-- The polynomial `c` of `R` is stored at `p`, as elements of `ℤ_q`. -/
def CStored (m : Mem) (p : Addr) (c : IPoly) : Prop := ∀ k < 256, coeffAt m p k = zw (ofInt c[k]!)

/-- What the proofs need of the entry state. -/
structure Pre (σ : State) : Prop where
  ok : SpOk (spOf σ) σ
  arg : InRegions (σ.rd ++ σ.wr) (stackArgAddr σ 0) 4
  tau_ge : 39 ≤ tau σ
  tau_le : tau σ ≤ 60

theorem X_length (σ : State) : (X σ).length = 272 := H_length _ _

theorem St_le (σ : State) (t : Nat) : (St σ t).2 ≤ 256 := bFold_le (by simp) _

theorem St_ge (σ : State) (t : Nat) : i0 σ ≤ (St σ t).2 :=
  bFold_ge (τ := tau σ) (h := signs (X σ)) (Vector.replicate n 0, i0 σ) _

/-- The sign bits not yet used, from their value. -/
abbrev Sg (σ : State) (i : Nat) (s : State) : Prop :=
  (s.gpr .r1).toNat + 2 ^ 32 * (s.gpr .r4).toNat = Wn σ / 2 ^ (i - i0 σ)

/-! ## Zeroing -/

/-- After `k` iterations of the zeroing loop. -/
structure ZAt (σ : State) (k : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  r7 : s.gpr .r7 = σ.gpr .r2
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  r12 : s.gpr .r12 = 0
  r0 : s.gpr .r0 = σ.gpr .r3 + BitVec.ofNat 32 (4 * k)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (256 - k))
  zero : ∀ j < k, coeffAt s.mem (spOf σ).A j = 0

/-- After the zeroing. -/
structure ZDone (σ : State) (s : State) : Prop where
  env : Env (spOf σ) σ s
  r7 : s.gpr .r7 = σ.gpr .r2
  out : bytesAt s.mem ((spOf σ).at' 840) 272 = X σ
  st : CStored s.mem (spOf σ).A (Vector.replicate n 0)

theorem zInit_ok (s : State) :
    WP isa (.block [.mov .r12 (.imm 0), .mov .r0 (.reg .r5), .mov .r3 (.imm 256)]) s fun s' =>
      s'.gpr .r12 = 0 ∧ s'.gpr .r0 = s.gpr .r5 ∧ s'.gpr .r3 = BitVec.ofNat 32 256 ∧
        (∀ r, r ≠ .r12 → r ≠ .r0 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [and_self, and_true, true_and]
  exact fun r h12 h0 h3 => by simp [h12, h0, h3]

theorem zStep_ok (s : State) {a : Addr} (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (hw : InRegions s.wr a 4) :
    WP isa (.block [.str .r12 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]) s fun s' =>
      s'.mem = s.mem.writeW a (s.gpr .r12) ∧ s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 4 ∧
        s'.gpr .r3 = s.gpr .r3 - BitVec.ofNat 32 1 ∧ s'.z = (s.gpr .r3 - BitVec.ofNat 32 1 == 0) ∧
        (∀ r, r ≠ .r0 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [ha, hw, and_self, and_true, true_and]
  refine ⟨rfl, rfl, rfl, fun r h0 h3 => ?_⟩
  simp [h0, h3]

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

theorem zBody_ok {k : Nat} (hk : k < 256) {s : State} (h : ZAt σ k s) :
    WP isa (.block [.str .r12 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]) s fun s' =>
      ZAt σ (k + 1) s' ∧ s'.z = decide (k + 1 = 256) := by
  have ea : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = coeffAddr (spOf σ).A k := by
    rw [h.r0]; exact addr_coeff hp.fa (by omega) hk
  have hin : InRegions s.wr (coeffAddr (spOf σ).A k) 4 := by
    rw [h.env.wr, hp.wr]; exact ⟨(spOf σ).aR, by simp, coeff_contains _ hk⟩
  refine WP.mono (zStep_ok s ea hin) fun s' ⟨m, r0, r3, z, g, rd, wr, sp⟩ => ?_
  have hf : Frame [(spOf σ).aR] s.mem s'.mem := by
    rw [m]; exact (Frame.refl _ _).writeW (by simp) _ (coeff_contains _ hk)
  refine ⟨⟨h.env.step hp hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
    (g _ (by decide) (by decide)) (g _ (by decide) (by decide)) rd wr sp,
    by rw [g _ (by decide) (by decide)]; exact h.r7, ?_, by rw [g _ (by decide) (by decide)]; exact h.r12,
    by rw [r0, h.r0, ptr_add_add32, Nat.mul_succ], by rw [r3, h.r3]; exact count_sub (k := 1) hk, fun j hj => ?_⟩,
    by rw [z, h.r3]; exact count_z (k := 1) hk (by decide) (by decide)⟩
  · rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 272) (by omega))).symm) (by omega)]
    exact h.out
  · rw [m, coeffAt_writeW _ _ (by omega) hk, h.r12]
    by_cases e : k = j
    · rw [ifT e]
    · rw [ifF e]; exact h.zero j (by omega)

/-- The zeroing loop, from what the sponge leaves. -/
theorem zero_ok {s : State} (h : J6 136 272 (spOf σ) σ s) : WP isa bZero s (ZDone σ) := by
  refine WP.seq (WP.mono (zInit_ok s) fun s1 ⟨r12, r0, r3, g, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_ne (ZAt σ) (N := 256) (by decide) (fun k hk s h => zBody_ok hp hk h)
    (fun s h => ⟨h.env, h.r7, h.out, fun k hk => ?_⟩) ⟨h.env.same m (g _ (by decide) (by decide) (by decide))
      (g _ (by decide) (by decide) (by decide)) rd wr sp, by rw [g _ (by decide) (by decide) (by decide), h.r7],
      by rw [m, h.out]; exact (H_eq _ _).symm, r12, by rw [r0, h.env.r5]; simp, r3,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [h.zero k hk, getElem!_pos _ k (by simp only [n]; omega), Vector.getElem_replicate]
  rfl

end

end VG.Proof.MlDsa.Arm.Sample.Ball
