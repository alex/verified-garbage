import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr

/-!
# X25519 on x86-64: multiplication by `a24` with BMI2 and ADX, and `adx_ok`

`a24X o a`: `r8–r12 = a24 · [a]` through CF (as row 0 of a product), then
`r12` folded as 38; and the field multiplications `adx` satisfy `FieldOk`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem a24X_eq (o a : Nat) : a24X o a = ([.mov32 .rdx (.imm a24)] : List Instr) ++ (([clear] : List Instr) ++
    (([.mulx .r9 .r8 (.mem (sc a))] : List Instr) ++ (mulAcc .r9 .r10 (.mem (sc (a + 8))) ++
      (mulAcc .r10 .r11 (.mem (sc (a + 16))) ++ (mulAcc .r11 .r12 (.mem (sc (a + 24))) ++
        (([.adcx .r12 (.reg .rbp)] : List Instr) ++ (([.mov32 .rdx (.imm 38)] : List Instr) ++
          (([.mulx .rcx .rax (.reg .r12)] : List Instr) ++ (carry38 ++ store4 o))))))))) := by
  simp only [a24X, List.append_assoc]; rfl

/-- `[o] = a24 · [a]`. -/
theorem a24X_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (a24X o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = Spec.X25519.a24 * F s.mem base a := by
  rw [a24X_eq, WP.block_append_iff]
  refine WP.mono (movRdxImm_ok s a24) fun s1 ⟨d1, _, _, k1⟩ => ?_
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
  rw [WP.block_append_iff]
  refine WP.mono (carryC_ok s6 hc6 z6) fun s7 ⟨c7, _, _, e7, k7⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movRdxImm_ok s7 38) fun s8 ⟨d8, _, _, k8⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulx_ok s8 rfl (noImm_reg _) (by decide)) fun s9 ⟨e9, _, _, k9⟩ => ?_
  -- `rdx = a24` for the products, and the memory they read.
  have D : ∀ x : State, x.gpr .rdx = s1.gpr .rdx → (x.gpr .rdx).toNat = 121665 :=
    fun x h => h ▸ d1
  have D2 := D s2 (k2.1 _ (by decide))
  have D3 := D s3 ((k3.1 _ (by decide)).trans (k2.1 _ (by decide)))
  have D4 := D s4 ((k4.1 _ (by decide)).trans ((k3.1 _ (by decide)).trans (k2.1 _ (by decide))))
  have D5 := D s5 ((k5.1 _ (by decide)).trans ((k4.1 _ (by decide)).trans
    ((k3.1 _ (by decide)).trans (k2.1 _ (by decide)))))
  have M2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have M3 : s3.mem = s.mem := k3.2.1.trans M2
  have M4 : s4.mem = s.mem := k4.2.1.trans M3
  have M5 : s5.mem = s.mem := k5.2.1.trans M4
  rw [D2, M2] at e3
  rw [D3, M3] at e4
  rw [D4, M4] at e5
  rw [D5, M5] at e6
  rw [show (s8.gpr .rdx).toNat = 38 from d8] at e9
  simp only [Bool.toNat_false, Nat.add_zero] at e4
  -- `r8–r11 + 2²⁵⁶ r12 = a24 · [a]`, so `r12 < a24` and `rax = 38 r12`.
  have hv : val4 (s7.gpr .r8) (s7.gpr .r9) (s7.gpr .r10) (s7.gpr .r11) +
      2 ^ 256 * (s7.gpr .r12).toNat = 121665 * fe s.mem base a := by
    have hA := fe_lt s.mem base a
    simp only [X86_64.fe, val4] at hA ⊢
    rw [k7.1 .r8 (by decide), k6.1 .r8 (by decide), k5.1 .r8 (by decide), k4.1 .r8 (by decide),
      k7.1 .r9 (by decide), k6.1 .r9 (by decide), k5.1 .r9 (by decide), k7.1 .r10 (by decide),
      k6.1 .r10 (by decide), k7.1 .r11 (by decide)]
    have := Bool.toNat_le c7
    omega
  have h12 : (s7.gpr .r12).toNat < 121665 := by
    have hA := fe_lt s.mem base a
    simp only [val4] at hv
    omega
  rw [k8.1 .r12 (by decide)] at e9
  have hax : (s9.gpr .rax).toNat = 38 * (s7.gpr .r12).toNat := by
    have := (s9.gpr .rax).isLt
    omega
  have hs9 := ((((hs5.of_keeps k6 (by decide)).of_keeps k7 (by decide)).of_keeps k8
    (by decide)).of_keeps k9 (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (carry38_ok s9 (by omega)) fun s10 ⟨e10, k10⟩ => ?_
  have hs10 := hs9.of_keeps k10 (by decide)
  refine WP.mono (store4_ok hs10 ho) fun s11 ⟨m11, g11, rd11, wr11⟩ => ?_
  have K : Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s10 :=
    (((((((((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide))).trans (k5.mono (by decide))).trans (k6.mono (by decide))).trans
      (k7.mono (by decide))).trans (k8.mono (by decide))).trans (k9.mono (by decide))).trans
      (k10.mono (by decide))
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g11, K.1 r (by simp [hr])]
  · rw [rd11, K.2.2.1]
  · rw [wr11, K.2.2.2]
  · rw [m11, K.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_a24
    rw [m11, fe_st4 _ _ (by omega), e10, hax, k9.1 .r8 (by decide), k9.1 .r9 (by decide),
      k9.1 .r10 (by decide), k9.1 .r11 (by decide), k8.1 .r8 (by decide), k8.1 .r9 (by decide),
      k8.1 .r10 (by decide), k8.1 .r11 (by decide), ← fold256, hv]

/-- The field multiplications with BMI2 and ADX. -/
theorem adx_ok : FieldOk adx where
  mul hs _ _ _ ho ha hb := mulX_ok hs ho ha hb
  sqr hs _ _ ho ha := sqrX_ok hs ho ha
  a24 hs _ _ ho ha := a24X_ok hs ho ha

end VG.Proof.X25519.X86_64
