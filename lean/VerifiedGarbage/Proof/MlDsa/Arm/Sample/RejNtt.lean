import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
import VerifiedGarbage.Impl.MlDsa.Arm.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_rej_ntt_poly`, correctness

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`G(ρ, 1008)` (`J6`), and the loop, iteration `t` of which starts from `LAt σ
t`, with the coefficients `rnFold` samples from the first `3t` bytes of output
stored. An iteration loads the value of its 3 bytes and tests `j ≥ 256`
(`pieceA`), stores it if `j < 256` and it is less than `q` (`pieceB`, what
`rnStep` does), and steps (`pieceC`).
-/

namespace VG.Proof.MlDsa.Arm.Sample.RejNtt

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- The call, from the entry state: `seed = r0`, `a = r1`, `scratch = r2`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r0, 34, σ.gpr .r2, σ.gpr .r1, 0⟩

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r0)) 34

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := G (B σ) 1008

/-- Byte `i` of the XOF output. -/
abbrev Xb (σ : State) (i : Nat) : Byte := (X σ).getD i 0

/-- The coefficients sampled after `t` iterations. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := rnFold [] ((X σ).take (3 * t))

/-- The value of 3 bytes, as the code computes it. -/
def rnw (b₀ b₁ b₂ : Byte) : BitVec 32 :=
  b₀.setWidth 32 + (b₂.setWidth 32 <<< 25) >>> 9 + b₁.setWidth 32 <<< 8

theorem rnw_toNat (b₀ b₁ b₂ : Byte) : (rnw b₀ b₁ b₂).toNat = rnZ b₀ b₁ b₂ := by
  have h0 := b₀.isLt
  have h1 := b₁.isLt
  have h2 := b₂.isLt
  unfold rnw rnZ
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
    setWidth32_toNat, setWidth32_toNat, setWidth32_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq]
  omega

/-- The value of the 3 bytes of iteration `t`. -/
abbrev V (σ : State) (t : Nat) : BitVec 32 := rnw (Xb σ (3 * t)) (Xb σ (3 * t + 1)) (Xb σ (3 * t + 2))

theorem V_lt (σ : State) (t : Nat) : (V σ t).toNat < 2 ^ 23 := by
  rw [rnw_toNat]; unfold rnZ
  have := (Xb σ (3 * t)).isLt; have := (Xb σ (3 * t + 1)).isLt; have := (Xb σ (3 * t + 2)).isLt
  omega

theorem X_length (σ : State) : (X σ).length = 1008 := G_length _ _

theorem take_add_three (L : List Byte) {i : Nat} (h : i + 3 ≤ L.length) :
    L.take (i + 3) = L.take i ++ [L.getD i 0, L.getD (i + 1) 0, L.getD (i + 2) 0] := by
  rw [List.take_add, List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < L.length by omega), List.getElem?_eq_getElem (show i + 1 < L.length by omega),
    List.getElem?_eq_getElem (show i + 2 < L.length by omega), Option.getD_some]

theorem Lt_succ (σ : State) {t : Nat} (ht : t < 336) :
    Lt σ (t + 1) = rnStep (Lt σ t) (Xb σ (3 * t)) (Xb σ (3 * t + 1)) (Xb σ (3 * t + 2)) := by
  simp only [Lt]
  rw [show 3 * (t + 1) = 3 * t + 3 by omega, take_add_three _ (by rw [X_length]; omega),
    rnFold_snoc _ (by rw [List.length_take, X_length]; omega)]

theorem Lt_length_le (σ : State) (t : Nat) : (Lt σ t).length ≤ 256 := rnFold_length_le (by simp) _

/-- At the start of iteration `t`. -/
structure LAt (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 1008 = X σ
  r0 : s.gpr .r0 = σ.gpr .r2 + BitVec.ofNat 32 (840 + 3 * t)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (Lt σ t).length
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (336 - t))
  r7 : s.gpr .r7 = BitVec.ofNat 32 8380417
  st : Stored s.mem (spOf σ).A (Lt σ t)

/-- After the value of the 3 bytes and the test of `j`. -/
structure M1 (σ : State) (t : Nat) (s : State) : Prop where
  lat : LAt σ t s
  r10 : s.gpr .r10 = V σ t
  z : s.z = decide (256 ≤ (Lt σ t).length)

/-- After the test of the value, if `j < 256`. -/
structure T1 (σ : State) (t : Nat) (s : State) : Prop where
  lat : LAt σ t s
  r10 : s.gpr .r10 = V σ t
  len : (Lt σ t).length < 256
  z : s.z = decide (8380417 ≤ (V σ t).toNat)

/-- After the coefficient of iteration `t`. -/
structure M2 (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 1008 = X σ
  r0 : s.gpr .r0 = σ.gpr .r2 + BitVec.ofNat 32 (840 + 3 * t)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (Lt σ (t + 1)).length
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (336 - t))
  r7 : s.gpr .r7 = BitVec.ofNat 32 8380417
  st : Stored s.mem (spOf σ).A (Lt σ (t + 1))

/-- `LAt` after a block that writes no memory and keeps `r0`, `r2`, `r3`,
`r5`, `r6` and `r7`. -/
theorem LAt.same {σ s s' : State} {t : Nat} (h : LAt σ t s) (hm : s'.mem = s.mem)
    (g : ∀ r ∈ [Reg.r0, .r2, .r3, .r5, .r6, .r7], s'.gpr r = s.gpr r) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (sp : s'.sp = s.sp) : LAt σ t s' :=
  ⟨h.env.same hm (g .r5 (by simp)) (g .r6 (by simp)) rd wr sp, by rw [hm]; exact h.out,
    (g .r0 (by simp)).trans h.r0, (g .r2 (by simp)).trans h.r2, (g .r3 (by simp)).trans h.r3,
    (g .r7 (by simp)).trans h.r7, by rw [hm]; exact h.st⟩

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- Byte `k` of iteration `t`. -/
theorem byte_ok {t : Nat} (ht : t < 336) {s : State} (h : LAt σ t s) {k : Nat} (hk : k < 3) :
    State.addr (s.gpr .r0 + BitVec.ofNat 32 k) = (spOf σ).at' (840 + (3 * t + k)) ∧
      InRegions (s.rd ++ s.wr) ((spOf σ).at' (840 + (3 * t + k))) 1 ∧
      s.mem ((spOf σ).at' (840 + (3 * t + k))) = Xb σ (3 * t + k) := by
  refine ⟨?_, inScrRd hp h.env (by omega), ?_⟩
  · rw [h.r0, ptr_add_add32, show 840 + 3 * t + k = 840 + (3 * t + k) by omega]; exact at_eq hp (by omega)
  · have := congrArg (fun L => L.getD (3 * t + k) 0) h.out
    rw [MlKem.bytesAt_getD _ _ (by omega), add_ofNat_add] at this
    exact this

omit hp in
theorem load_ok (s : State) {A₀ A₁ A₂ : Addr} {b₀ b₁ b₂ : Byte}
    (a0 : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = A₀) (a1 : State.addr (s.gpr .r0 + BitVec.ofNat 32 1) = A₁)
    (a2 : State.addr (s.gpr .r0 + BitVec.ofNat 32 2) = A₂) (i0 : InRegions (s.rd ++ s.wr) A₀ 1)
    (i1 : InRegions (s.rd ++ s.wr) A₁ 1) (i2 : InRegions (s.rd ++ s.wr) A₂ 1) (v0 : s.mem A₀ = b₀)
    (v1 : s.mem A₁ = b₁) (v2 : s.mem A₂ = b₂) :
    WP isa (.block rnLoad) s fun s' => s'.gpr .r10 = rnw b₀ b₁ b₂ ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [rnLoad, rnw, a0, a1, a2, i0, i1, i2, v0, v1, v2, and_self, and_true, true_and]
  exact fun r h8 h9 h10 => by simp [h8, h9, h10]

theorem pieceA {t : Nat} (ht : t < 336) {s : State} (h : LAt σ t s) :
    WP isa (.block (rnLoad ++ jFull)) s (M1 σ t) := by
  obtain ⟨a0, i0, v0⟩ := byte_ok hp ht h (k := 0) (by decide)
  obtain ⟨a1, i1, v1⟩ := byte_ok hp ht h (k := 1) (by decide)
  obtain ⟨a2, i2, v2⟩ := byte_ok hp ht h (k := 2) (by decide)
  rw [Nat.add_zero] at v0
  rw [WP.block_append_iff]
  refine WP.mono (load_ok s a0 a1 a2 i0 i1 i2 v0 v1 v2) fun s1 ⟨g10, g1, m1, rd1, wr1, sp1⟩ => ?_
  have l1 : LAt σ t s1 := h.same m1 (fun r hr => g1 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide) (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) rd1 wr1 sp1
  refine WP.mono (jFull_ok s1 l1.r2 (by have := Lt_length_le σ t; omega)) fun s2 ⟨z2, g2, m2, rd2, wr2, sp2⟩ =>
    ⟨l1.same m2 (fun r hr => g2 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
      rd2 wr2 sp2, by rw [g2 _ (by decide), g10], z2⟩

omit hp in
theorem tryA {t : Nat} {s : State} (h : M1 σ t s) (hz : s.z = false) :
    WP isa (.block [.dp .sub .r11 .r10 (.reg .r7), .mov .r11 (.shifted .r11 .lsr 31), .cmp .r11 (.imm 0)]) s
      (T1 σ t) := by
  have hl : (Lt σ t).length < 256 := by
    have := h.z; rw [hz] at this; simp at this; omega
  have hv := V_lt σ t
  refine WP.mono (sgn_ok s .r10 (.reg .r7) (y := BitVec.ofNat 32 8380417) (by simp [Op2.eval, h.lat.r7])
    (by rw [h.r10]; omega) (by decide)) fun s' ⟨z, g, m, rd, wr, sp⟩ => ⟨h.lat.same m (fun r hr => g r (by
      simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) rd wr sp,
    by rw [g _ (by decide), h.r10], hl, by rw [z, h.r10]; rfl⟩

omit hp in
theorem zw_V {σ : State} {t : Nat} (hq : (V σ t).toNat < q) : zw (Fin.ofNat q (V σ t).toNat) = V σ t := by
  apply BitVec.eq_of_toNat_eq
  rw [zw_toNat, Fin.val_ofNat, Nat.mod_eq_of_lt hq]

theorem tryB {t : Nat} (ht : t < 336) {s : State} (h : T1 σ t s) :
    WP isa (.ite .eq (.block []) (.block (storeJ .r10))) s (M2 σ t) := by
  have hstep := Lt_succ σ ht
  rw [rnStep, ifT (show (Lt σ t).length < 256 from h.len), ← rnw_toNat] at hstep
  refine WP.ite s.z rfl (fun e => ?_) (fun e => ?_)
  · -- rejected
    have hq : ¬ (V σ t).toNat < q := by
      have := h.z; rw [e] at this; simp at this; show ¬ _ < 8380417; omega
    rw [ifF hq] at hstep
    have l := h.lat
    exact WP.block_nil ⟨l.env, l.out, l.r0, by rw [hstep]; exact l.r2, l.r3, l.r7, by rw [hstep]; exact l.st⟩
  · have hq : (V σ t).toNat < q := by
      have := h.z; rw [e] at this; simp at this; show _ < 8380417; omega
    rw [ifT hq] at hstep
    have l := h.lat
    refine WP.mono (storeJ_stored hp l.env (by decide) l.r2 h.len l.st (x := Fin.ofNat q (V σ t).toNat)
      (by rw [h.r10, zw_V hq])) fun s' ⟨st, r2, g, _, he, hf⟩ => ⟨he, ?_, by rw [g _ (by decide) (by decide), l.r0],
        by rw [hstep]; exact r2, by rw [g _ (by decide) (by decide), l.r3], by rw [g _ (by decide) (by decide), l.r7],
        by rw [hstep]; exact st⟩
    rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 1008) (by omega))).symm) (by omega)]
    exact l.out

theorem pieceB {t : Nat} (ht : t < 336) {s : State} (h : M1 σ t s) :
    WP isa (.ite .eq (.block []) rnTry) s (M2 σ t) := by
  refine WP.ite s.z rfl (fun e => ?_) (fun e => ?_)
  · -- `j = 256`: nothing changes
    have hl : (Lt σ t).length = 256 := by
      have := h.z; rw [e] at this; simp at this; have := Lt_length_le σ t; omega
    have hstep : Lt σ (t + 1) = Lt σ t := by rw [Lt_succ σ ht, rnStep_full hl]
    have l := h.lat
    exact WP.block_nil ⟨l.env, l.out, l.r0, by rw [hstep]; exact l.r2, l.r3, l.r7, by rw [hstep]; exact l.st⟩
  · exact WP.seq (WP.mono (tryA h e) fun _ h1 => tryB hp ht h1)

omit hp in
theorem pieceC {t : Nat} (ht : t < 336) {s : State} (h : M2 σ t s) :
    WP isa (.block (step 3)) s fun s' => LAt σ (t + 1) s' ∧ s'.z = decide (t + 1 = 336) := by
  refine WP.mono (step_ok s (k := 3) (by decide)) fun s' ⟨r0, r3, z, g, m, rd, wr, sp⟩ =>
    ⟨⟨h.env.same m (g _ (by decide) (by decide)) (g _ (by decide) (by decide)) rd wr sp, by rw [m]; exact h.out,
      ?_, by rw [g _ (by decide) (by decide)]; exact h.r2, by rw [r3, h.r3]; exact count_sub (k := 1) ht,
      by rw [g _ (by decide) (by decide)]; exact h.r7, by rw [m]; exact h.st⟩, ?_⟩
  · rw [r0, h.r0, ptr_add_add32, show 840 + 3 * t + 3 = 840 + 3 * (t + 1) by omega]
  · rw [z, h.r3]; exact count_z (k := 1) ht (by decide) (by decide)

/-- An iteration. -/
theorem body_ok {t : Nat} (ht : t < 336) {s : State} (h : LAt σ t s) :
    WP isa rnBody s fun s' => LAt σ (t + 1) s' ∧ s'.z = decide (t + 1 = 336) :=
  WP.seq (WP.mono (pieceA hp ht h) fun _ h1 => WP.seq (WP.mono (pieceB hp ht h1) fun _ h2 => pieceC ht h2))

end


/-! ## The whole function -/

theorem init_ok (s : State) :
    WP isa (.block [.dp .add .r0 .r6 (.imm 840), .mov .r2 (.imm 0), .mov .r3 (.imm 336), .movw .r7 0xE001,
      .movt .r7 0x7F]) s fun s' => s'.gpr .r0 = s.gpr .r6 + BitVec.ofNat 32 840 ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧
        s'.gpr .r3 = BitVec.ofNat 32 336 ∧ s'.gpr .r7 = BitVec.ofNat 32 8380417 ∧ s'.gpr .r5 = s.gpr .r5 ∧
        s'.gpr .r6 = s.gpr .r6 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [and_self, and_true, true_and]
  rfl

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

omit hp in
theorem lat0 {s : State} (h : J6 168 1008 (spOf σ) σ s) : WP isa (.block [.dp .add .r0 .r6 (.imm 840),
    .mov .r2 (.imm 0), .mov .r3 (.imm 336), .movw .r7 0xE001, .movt .r7 0x7F]) s (LAt σ 0) :=
  WP.mono (init_ok s) fun s' ⟨r0, r2, r3, r7, g5, g6, m, rd, wr, sp⟩ =>
    ⟨h.env.same m g5 g6 rd wr sp, by rw [m, h.out]; exact (G_eq _ _).symm, by rw [r0, h.env.r6],
      by rw [r2]; rfl, by rw [r3], r7, by rw [m]; exact stored_nil _ _⟩

theorem loop_ok {s : State} (h : J6 168 1008 (spOf σ) σ s) : WP isa rnLoop s (LAt σ 336) :=
  WP.seq (WP.mono (lat0 h) fun _ h0 =>
    wp_loop_ne (LAt σ) (N := 336) (by decide) (fun t ht s h => body_ok hp ht h) (fun _ h => h) h0)

omit hp in
theorem Lt_all : Lt σ 336 = rnFold [] (X σ) := by
  simp only [Lt]; rw [List.take_of_length_le (by rw [X_length])]

theorem end_ok {s : State} (h : LAt σ 336 s) :
    WP isa (.block (retJ ++ epi)) s fun s' => s'.gpr .r0 = (if (rnFold [] (X σ)).length = 256 then 1 else 0) ∧
      ((rnFold [] (X σ)).length = 256 → PolyIs s'.mem (State.addr (σ.gpr .r1)) (toPoly (rnFold [] (X σ)))) ∧
      abiPreserved σ s' :=
  WP.mono (retEpi_ok hp h.env h.r2 (Lt_length_le _ _)) fun s' ⟨h0, hm, ha⟩ =>
    ⟨by rw [h0, Lt_all], fun hf => by rw [hm]; exact Lt_all ▸ stored_polyIs h.st (by rw [Lt_all]; exact hf),
      ha⟩

/-- The function, from an entry state whose regions are those of a call. -/
theorem correct : WP isa Impl.MlDsa.Arm.Sample.rejNTT σ fun s' =>
    s'.gpr .r0 = (if (rnFold [] (X σ)).length = 256 then 1 else 0) ∧
      ((rnFold [] (X σ)).length = 256 → PolyIs s'.mem (State.addr (σ.gpr .r1)) (toPoly (rnFold [] (X σ)))) ∧
      abiPreserved σ s' :=
  WP.seq (WP.mono (pro_rn hp rfl rfl rfl rfl rfl) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok hp (rate := 168) (outlen := 1008) (by decide) (by decide) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (loop_ok hp h2) fun _ h3 => end_ok hp h3)))

end

end VG.Proof.MlDsa.Arm.Sample.RejNtt
