import VerifiedGarbage.Proof.X25519.X86_64.Adx.Steps
import VerifiedGarbage.Proof.X25519.X86_64.Env

/-!
# X25519 on x86-64: multiplication with BMI2 and ADX

Untrusted: everything here is checked by Lean. The rows of a product
(`rowX0`, and `rowX` for any five registers), the reduction (`reduceX`), and
the multiplication `mulX o a b`, as `mul_ok` states `mul`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem noImm_mem (m : MemOp) : ∀ n, (Src.mem m) ≠ .imm n := fun _ h => nomatch h
theorem noImm_reg (r : Reg) : ∀ n, (Src.reg r) ≠ .imm n := fun _ h => nomatch h

/-- A number times four words, word by word. -/
theorem mul_val4 (v x y z w : Nat) : v * (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) =
    v * x + 2 ^ 64 * (v * y) + 2 ^ 128 * (v * z) + 2 ^ 192 * (v * w) := by
  simp only [Nat.mul_add, Nat.mul_left_comm v]

theorem fe_lt (m : Mem) (base : Addr) (a : Nat) : fe m base a < 2 ^ 256 := by
  simp only [X86_64.fe, val4]
  have := (word m base a).isLt; have := (word m base (a + 8)).isLt
  have := (word m base (a + 16)).isLt; have := (word m base (a + 24)).isLt
  omega

/-- A word times four words. -/
theorem word_mul_lt (w : BitVec 64) (f : Nat) (hf : f < 2 ^ 256) :
    w.toNat * f ≤ (2 ^ 64 - 1) * (2 ^ 256 - 1) :=
  Nat.mul_le_mul (by have := w.isLt; omega) (by omega)

/-! ## Row 0 -/

theorem rowX0_eq (a b : Nat) : rowX0 a b = ([.mov .rdx (.mem (sc b))] : List Instr) ++ (([clear] : List Instr) ++
    (([.mulx .r9 .r8 (.mem (sc a))] : List Instr) ++ (mulAcc .r9 .r10 (.mem (sc (a + 8))) ++
      (mulAcc .r10 .r11 (.mem (sc (a + 16))) ++ (mulAcc .r11 .r12 (.mem (sc (a + 24))) ++
        ([.adcx .r12 (.reg .rbp)] : List Instr)))))) := rfl

/-- Row 0: `r8–r12 = b₀ · a`. -/
theorem rowX0_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat} (ha : Slot a)
    (hb : b + 8 ≤ 4096) :
    WP isa (.block (rowX0 a b)) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * (s'.gpr .r12).toNat =
        (word s.mem base b).toNat * fe s.mem base a ∧
      s'.gpr .rdx = word s.mem base b ∧ s'.gpr .rbp = 0 ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rdx, .rbp] s s' := by
  rw [rowX0_eq, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (readSrc_sc hs hb)) fun s1 ⟨d1, _, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (clear_ok s1) fun s2 ⟨z2, c2, _, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok s2 (readSrc_sc hs2 (by omega)) (noImm_mem _) (by decide))
    fun s3 ⟨e3, c3, _, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulAcc_ok s3 (readSrc_sc hs3 (by omega)) (noImm_mem _) (c3.trans c2)
    (by decide) (by decide) (by decide)) fun s4 ⟨c4, hc4, _, e4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulAcc_ok s4 (readSrc_sc hs4 (by omega)) (noImm_mem _) hc4
    (by decide) (by decide) (by decide)) fun s5 ⟨c5, hc5, _, e5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulAcc_ok s5 (readSrc_sc hs5 (by omega)) (noImm_mem _) hc5
    (by decide) (by decide) (by decide)) fun s6 ⟨c6, hc6, _, e6, k6⟩ => ?_
  have z6 : s6.gpr .rbp = 0 := by
    rw [k6.1 _ (by decide), k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide), z2]
  refine WP.mono (carryC_ok s6 hc6 z6) fun s7 ⟨c7, _, _, e7, k7⟩ => ?_
  have K : Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rdx, .rbp] s s7 :=
    ((((((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide))).trans (k5.mono (by decide))).trans (k6.mono (by decide))).trans
      (k7.mono (by decide))
  -- `rdx` and the memory along the way.
  have D2 : s2.gpr .rdx = word s.mem base b := (k2.1 _ (by decide)).trans d1
  have D3 : s3.gpr .rdx = word s.mem base b := (k3.1 _ (by decide)).trans D2
  have D4 : s4.gpr .rdx = word s.mem base b := (k4.1 _ (by decide)).trans D3
  have D5 : s5.gpr .rdx = word s.mem base b := (k5.1 _ (by decide)).trans D4
  have M2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have M3 : s3.mem = s.mem := k3.2.1.trans M2
  have M4 : s4.mem = s.mem := k4.2.1.trans M3
  have M5 : s5.mem = s.mem := k5.2.1.trans M4
  refine ⟨?_, by rw [k7.1 _ (by decide), k6.1 _ (by decide), D5], by rw [k7.1 _ (by decide), z6],
    K⟩
  rw [D2, M2] at e3
  rw [D3, M3] at e4
  rw [D4, M4] at e5
  rw [D5, M5] at e6
  have b1 := word_mul_lt (word s.mem base b) _ (fe_lt s.mem base a)
  simp only [X86_64.fe, val4, mul_val4] at b1 ⊢
  rw [k7.1 .r8 (by decide), k6.1 .r8 (by decide), k5.1 .r8 (by decide), k4.1 .r8 (by decide),
    k7.1 .r9 (by decide), k6.1 .r9 (by decide), k5.1 .r9 (by decide), k7.1 .r10 (by decide),
    k6.1 .r10 (by decide), k7.1 .r11 (by decide)]
  simp only [Bool.toNat_false, Nat.add_zero] at e4
  have := Bool.toNat_le c7
  omega

/-! ## Rows 1 to 3 -/

/-- `r ∉ [...]` and `a ≠ b` from the distinctness hypotheses in context. -/
local macro "nm" : tactic =>
  `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, ne_eq] <;>
    (repeat' constructor) <;>
    first | with_reducible assumption | exact Ne.symm (by with_reducible assumption) | decide))

/-- A row `i ≥ 1`, for any five registers. -/
def rowR' (a b i : Nat) (r0 r1 r2 r3 r4 : Reg) : List Instr :=
  [.mov .rdx (.mem (sc (b + 8 * i)))] ++ ([clear] ++ (madd r0 r1 (.mem (sc a)) ++
    (madd r1 r2 (.mem (sc (a + 8))) ++ (madd r2 r3 (.mem (sc (a + 16))) ++
      maddLast r3 r4 (.mem (sc (a + 24)))))))

theorem rowX_eq (a b i : Nat) :
    rowX a b i = rowR' a b i (t i) (t (i + 1)) (t (i + 2)) (t (i + 3)) (t (i + 4)) := by
  simp only [rowX, rowR', List.append_assoc]; rfl

/-- A row: `r0–r3 + b_i · a` into `r0–r4`. -/
theorem rowR'_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat} (ha : Slot a)
    (hb : b + 8 * i + 8 ≤ 4096) {r0 r1 r2 r3 r4 : Reg}
    (hd : ([r0, r1, r2, r3, r4, .rax, .rcx, .rdx, .rbp, .rdi] : List Reg).Nodup) :
    WP isa (.block (rowR' a b i r0 r1 r2 r3 r4)) s fun s' =>
      val4 (s'.gpr r0) (s'.gpr r1) (s'.gpr r2) (s'.gpr r3) + 2 ^ 256 * (s'.gpr r4).toNat =
        val4 (s.gpr r0) (s.gpr r1) (s.gpr r2) (s.gpr r3) +
          (word s.mem base (b + 8 * i)).toNat * fe s.mem base a ∧
      Keeps [r0, r1, r2, r3, r4, .rax, .rcx, .rdx, .rbp] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h0a, h0c, h0d, h0b, h0i⟩, ⟨h12, h13, h14, h1a, h1c, h1d, h1b, h1i⟩,
    ⟨h23, h24, h2a, h2c, h2d, h2b, h2i⟩, ⟨h34, h3a, h3c, h3d, h3b, h3i⟩,
    ⟨h4a, h4c, h4d, h4b, h4i⟩, -⟩ := hd
  rw [rowR', WP.block_append_iff]
  refine WP.mono (movRdx_ok s (readSrc_sc hs hb)) fun s1 ⟨d1, _, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (clear_ok s1) fun s2 ⟨z2, c2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s2 (readSrc_sc hs2 (by omega)) (noImm_mem _) c2 o2
    (by nm) (by nm) (by nm) (by nm) (by nm)) fun s3 ⟨c3, o3, hc3, ho3, e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by nm)
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s3 (readSrc_sc hs3 (by omega)) (noImm_mem _) hc3 ho3
    (by nm) (by nm) (by nm) (by nm) (by nm)) fun s4 ⟨c4, o4, hc4, ho4, e4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by nm)
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s4 (readSrc_sc hs4 (by omega)) (noImm_mem _) hc4 ho4
    (by nm) (by nm) (by nm) (by nm) (by nm)) fun s5 ⟨c5, o5, hc5, ho5, e5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by nm)
  have z5 : s5.gpr .rbp = 0 := by
    rw [k5.1 _ (by nm), k4.1 _ (by nm), k3.1 _ (by nm), z2]
  refine WP.mono (maddLast_ok s5 (readSrc_sc hs5 (by omega)) (noImm_mem _) hc5 ho5 z5
    (by nm) (by nm) (by nm) (by nm) (by nm)) fun s6 ⟨c6, o6, _, _, e6, k6⟩ => ?_
  have K : Keeps [r0, r1, r2, r3, r4, .rax, .rcx, .rdx, .rbp] s s6 :=
    (((((k1.mono (by simp)).trans (k2.mono (by simp))).trans (k3.mono (by simp))).trans
      (k4.mono (by simp))).trans (k5.mono (by simp))).trans (k6.mono (by simp))
  refine ⟨?_, K⟩
  -- `rdx`, the memory and the registers along the way.
  have D2 : s2.gpr .rdx = word s.mem base (b + 8 * i) := (k2.1 _ (by nm)).trans d1
  have D3 : s3.gpr .rdx = word s.mem base (b + 8 * i) := (k3.1 _ (by nm)).trans D2
  have D4 : s4.gpr .rdx = word s.mem base (b + 8 * i) := (k4.1 _ (by nm)).trans D3
  have D5 : s5.gpr .rdx = word s.mem base (b + 8 * i) := (k5.1 _ (by nm)).trans D4
  have M2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have M3 : s3.mem = s.mem := k3.2.1.trans M2
  have M4 : s4.mem = s.mem := k4.2.1.trans M3
  have M5 : s5.mem = s.mem := k5.2.1.trans M4
  rw [D2, M2, k2.1 r0 (by nm), k1.1 r0 (by nm), k2.1 r1 (by nm), k1.1 r1 (by nm)] at e3
  rw [D3, M3, k3.1 r2 (by nm), k2.1 r2 (by nm), k1.1 r2 (by nm)] at e4
  rw [D4, M4, k4.1 r3 (by nm), k3.1 r3 (by nm), k2.1 r3 (by nm), k1.1 r3 (by nm)] at e5
  rw [D5, M5] at e6
  have b1 := word_mul_lt (word s.mem base (b + 8 * i)) _ (fe_lt s.mem base a)
  have b2 : val4 (s.gpr r0) (s.gpr r1) (s.gpr r2) (s.gpr r3) < 2 ^ 256 := by
    simp only [val4]
    have := (s.gpr r0).isLt; have := (s.gpr r1).isLt; have := (s.gpr r2).isLt
    have := (s.gpr r3).isLt
    omega
  simp only [X86_64.fe, val4, mul_val4] at b1 b2 ⊢
  rw [k6.1 r0 (by nm), k5.1 r0 (by nm), k4.1 r0 (by nm), k6.1 r1 (by nm), k5.1 r1 (by nm),
    k6.1 r2 (by nm)]
  simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e3
  have := Bool.toNat_le c6; have := Bool.toNat_le o6
  omega

/-! ## The reduction -/

theorem reduceX_eq : reduceX = ([.mov32 .rdx (.imm 38)] : List Instr) ++ (([clear] : List Instr) ++ (madd .r8 .r9 (.reg .r12) ++
    (madd .r9 .r10 (.reg .r13) ++ (madd .r10 .r11 (.reg .r14) ++ (maddLast .r11 .r12 (.reg .r15) ++
      (([.mulx .rcx .rax (.reg .r12)] : List Instr) ++ carry38)))))) := rfl

open VG.Spec.X25519 (P) in
/-- `r8–r11 + 2²⁵⁶ r12–r15`, reduced into `r8–r11` (modulo `p`). -/
theorem reduceX_ok (s : State) :
    WP isa (.block reduceX) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          2 ^ 256 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)) % P ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [reduceX_eq, WP.block_append_iff]
  refine WP.mono (movRdxImm_ok s 38) fun s1 ⟨d1, _, _, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (clear_ok s1) fun s2 ⟨z2, c2, o2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s2 rfl (noImm_reg _) c2 o2 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s3 ⟨c3, o3, hc3, ho3, e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s3 rfl (noImm_reg _) hc3 ho3 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s4 ⟨c4, o4, hc4, ho4, e4, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (madd_ok s4 rfl (noImm_reg _) hc4 ho4 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s5 ⟨c5, o5, hc5, ho5, e5, k5⟩ => ?_
  have z5 : s5.gpr .rbp = 0 := by
    rw [k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide), z2]
  rw [WP.block_append_iff]
  refine WP.mono (maddLast_ok s5 rfl (noImm_reg _) hc5 ho5 z5 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s6 ⟨c6, o6, _, _, e6, k6⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok s6 rfl (noImm_reg _) (by decide)) fun s7 ⟨e7, _, _, k7⟩ => ?_
  -- `rdx = 38` along the way.
  have D : ∀ x : State, x.gpr .rdx = s1.gpr .rdx → (x.gpr .rdx).toNat = 38 := fun x h => h ▸ d1
  have D2 := D s2 (k2.1 _ (by decide))
  have D3 := D s3 ((k3.1 _ (by decide)).trans (k2.1 _ (by decide)))
  have D4 := D s4 ((k4.1 _ (by decide)).trans ((k3.1 _ (by decide)).trans (k2.1 _ (by decide))))
  have D5 := D s5 ((k5.1 _ (by decide)).trans ((k4.1 _ (by decide)).trans
    ((k3.1 _ (by decide)).trans (k2.1 _ (by decide)))))
  have D6 := D s6 ((k6.1 _ (by decide)).trans ((k5.1 _ (by decide)).trans ((k4.1 _ (by decide)).trans
    ((k3.1 _ (by decide)).trans (k2.1 _ (by decide))))))
  rw [D2, k2.1 .r12 (by decide), k1.1 .r12 (by decide), k2.1 .r8 (by decide), k1.1 .r8 (by decide),
    k2.1 .r9 (by decide), k1.1 .r9 (by decide)] at e3
  rw [D3, k3.1 .r13 (by decide), k2.1 .r13 (by decide), k1.1 .r13 (by decide),
    k3.1 .r10 (by decide), k2.1 .r10 (by decide), k1.1 .r10 (by decide)] at e4
  rw [D4, k4.1 .r14 (by decide), k3.1 .r14 (by decide), k2.1 .r14 (by decide),
    k1.1 .r14 (by decide), k4.1 .r11 (by decide), k3.1 .r11 (by decide), k2.1 .r11 (by decide),
    k1.1 .r11 (by decide)] at e5
  rw [D5, k5.1 .r15 (by decide), k4.1 .r15 (by decide), k3.1 .r15 (by decide),
    k2.1 .r15 (by decide), k1.1 .r15 (by decide)] at e6
  rw [D6] at e7
  simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e3
  -- The carry word `r12` is at most 38, so `rax = 38 r12` exactly.
  have hB : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
      38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) < 39 * 2 ^ 256 := by
    simp only [val4]
    have := (s.gpr .r8).isLt; have := (s.gpr .r9).isLt; have := (s.gpr .r10).isLt
    have := (s.gpr .r11).isLt; have := (s.gpr .r12).isLt; have := (s.gpr .r13).isLt
    have := (s.gpr .r14).isLt; have := (s.gpr .r15).isLt
    omega
  have hv : val4 (s6.gpr .r8) (s6.gpr .r9) (s6.gpr .r10) (s6.gpr .r11) +
      2 ^ 256 * (s6.gpr .r12).toNat =
        val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) := by
    rw [k6.1 .r8 (by decide), k5.1 .r8 (by decide), k4.1 .r8 (by decide), k6.1 .r9 (by decide),
      k5.1 .r9 (by decide), k6.1 .r10 (by decide)]
    simp only [val4] at hB ⊢
    have := (s6.gpr .r11).isLt; have := (s6.gpr .r12).isLt
    have := Bool.toNat_le c6; have := Bool.toNat_le o6
    omega
  have h12 : (s6.gpr .r12).toNat < 39 := by
    simp only [val4] at hv hB
    omega
  have hax : (s7.gpr .rax).toNat = 38 * (s6.gpr .r12).toNat := by
    have := (s7.gpr .rax).isLt
    omega
  refine WP.mono (carry38_ok s7 (by omega)) fun s8 ⟨e8, k8⟩ => ?_
  refine ⟨?_, ((((((((k1.mono (by decide)).trans (k2.mono (by decide))).trans
    (k3.mono (by decide))).trans (k4.mono (by decide))).trans (k5.mono (by decide))).trans
    (k6.mono (by decide))).trans (k7.mono (by decide))).trans (k8.mono (by decide)))⟩
  rw [e8, hax, k7.1 .r8 (by decide), k7.1 .r9 (by decide), k7.1 .r10 (by decide),
    k7.1 .r11 (by decide), ← fold256, hv, fold256]

/-! ## The multiplication -/

theorem mulX_eq (o a b : Nat) : mulX o a b = rowX0 a b ++ (rowR' a b 1 .r9 .r10 .r11 .r12 .r13 ++
    (rowR' a b 2 .r10 .r11 .r12 .r13 .r14 ++ (rowR' a b 3 .r11 .r12 .r13 .r14 .r15 ++
      (reduceX ++ store4 o)))) := by
  simp only [mulX, rowX_eq, List.append_assoc]; rfl

/-- `[o] = [a] · [b]`. -/
theorem mulX_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mulX o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b := by
  rw [mulX_eq, WP.block_append_iff]
  refine WP.mono (rowX0_ok hs ha (by omega)) fun s₁ ⟨e1, _, _, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (rowR'_ok hs₁ ha (by omega) (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (rowR'_ok hs₂ ha (by omega) (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (rowR'_ok hs₃ ha (by omega) (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduceX_ok s₄) fun s₅ ⟨e5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  refine WP.mono (store4_ok hs₅ ho) fun s₆ ⟨m6, g6, rd6, wr6⟩ => ?_
  have M : s₅.mem = s.mem := k5.2.1.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1)))
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g6, k5.1 r (by simp [*]), k4.1 r (by simp [*]), k3.1 r (by simp [*]),
      k2.1 r (by simp [*]), k1.1 r (by simp [*])]
  · rw [rd6, k5.2.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
  · rw [wr6, k5.2.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]
  · rw [m6, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul
    rw [m6, fe_st4 _ _ (by omega), e5]
    -- Every row read the same memory.
    rw [k1.2.1] at e2
    rw [k2.2.1, k1.2.1] at e3
    rw [k3.2.1, k2.2.1, k1.2.1] at e4
    have r1 := k2.1 .r8 (by decide); have r2 := k3.1 .r8 (by decide)
    have r3 := k4.1 .r8 (by decide); have q2 := k3.1 .r9 (by decide)
    have q3 := k4.1 .r9 (by decide); have q4 := k4.1 .r10 (by decide)
    congr 1
    have hb' : fe s.mem base b = val4 (word s.mem base b) (word s.mem base (b + 8))
        (word s.mem base (b + 16)) (word s.mem base (b + 24)) := rfl
    rw [hb']
    simp only [val4] at e1 e2 e3 e4 ⊢
    rw [mul_val4 (fe s.mem base a), Nat.mul_comm (fe s.mem base a), Nat.mul_comm (fe s.mem base a),
      Nat.mul_comm (fe s.mem base a), Nat.mul_comm (fe s.mem base a)]
    simp only [Nat.mul_one, Nat.reduceMul] at e2 e3 e4
    rw [r3, r2, r1, q3, q2, q4]
    omega_using [e1, e2, e3, e4]

end VG.Proof.X25519.X86_64
