import VerifiedGarbage.Proof.MlKem1024.X86.Pack

/-!
# ML-KEM-1024 on x86 (32-bit): loading bytes and decompressing coefficients

`decompOp` computes the decompress formula of `Compress1024.lean`
(`decomp_spec`), which `decSt` stores (`decSt_spec`); `bySteps` and `ldW`
combine bytes into `ebx` (`bySteps_spec`, `ldW_spec`), as the number `pk 8`
whose base-2⁸ digits they are.
-/

namespace VG.Proof.MlKem1024.X86

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

theorem dv_lt' {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) {y : Nat} (hy : y < 2 ^ d) : dv d y < q :=
  (decompress1024_val hd hy).2

theorem dv_eq' {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) {y : Nat} (hy : y < 2 ^ d) :
    dv d y = (decompress d y).val := (decompress1024_val hd hy).1.symm

/-- `decompOp d` computes `dv d y` in `eax` from `eax = y < 2ᵈ`, changing only `eax`, `edx` and
the flags. -/
theorem decomp_spec' {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) (is : List Instr) (s : State)
    (P : State → Prop) {y : Nat} (hy : y < 2 ^ d) (h : (s.gpr .eax).toNat = y)
    (k : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = dv d y → WP isa (.block is) s' P) :
    WP isa (.block (decompOp d ++ is)) s P := by
  have hd' : 1 ≤ d ∧ d ≤ 31 ∧ y < 2048 := by
    rcases mem_compressWidths1024 hd with rfl | rfl <;> refine ⟨by decide, by decide, ?_⟩ <;> omega
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [decompOp, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, execMul, readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    Option.map_some, ite_true, ite_false, Option.some.injEq, exists_eq_left', hd'.1, hd'.2.1, and_self]
  refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · simp only [ite_true]
    have hp : 2 ^ (d - 1) ≤ 1024 := by
      rcases mem_compressWidths1024 hd with rfl | rfl <;> decide
    rw [toNat_shr]
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, h]
    rw [show (3329 : BitVec 32).toNat = 3329 from rfl, Nat.mod_eq_of_lt (a := y * 3329) (by omega),
      Nat.mod_eq_of_lt (a := 2 ^ (d - 1)) (by omega), Nat.mod_eq_of_lt (by omega), dv, q_eq, Nat.mul_comm y]

/-- `decSt d j` writes `dv d y` to `[edi + 4j]`, from `eax = y < 2ᵈ`. -/
theorem decSt_spec {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) (j : Nat) (is : List Instr)
    (s : State) (P : State → Prop) {y : Nat} (hy : y < 2 ^ d) (h : (s.gpr .eax).toNat = y)
    (hin : InRegions s.wr (s.ea (at_ .edi (4 * j))) 4)
    (k : ∀ s', Regs [.eax, .edx] s s' →
      s'.mem = s.mem.writeW (s.ea (at_ .edi (4 * j))) (BitVec.ofNat 32 (dv d y)) → WP isa (.block is) s' P) :
    WP isa (.block (decSt d j ++ is)) s P := by
  rw [decSt, List.append_assoc]
  refine decomp_spec' hd _ s P hy h fun s₁ o₁ v₁ => ?_
  have ea₁ : s₁.ea (at_ .edi (4 * j)) = s.ea (at_ .edi (4 * j)) := by
    simp only [State.ea, at_, o₁.gpr .edi (by decide)]
  refine wp_store (by rw [ea₁, o₁.wr]; exact hin) ?_
  refine k _ ⟨fun r hr => o₁.gpr r hr, o₁.rd, o₁.wr⟩ ?_
  show s₁.mem.writeW (s₁.ea (at_ .edi (4 * j))) (s₁.gpr .eax) = _
  rw [ea₁, o₁.mem, eq_ofNat_of_toNat v₁]

/-- Byte `i` from `esi`: at `[esi + i]`, readable, `v`. -/
structure Byt (s : State) (i v : Nat) : Prop where
  in_ : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi i)) 1
  val : (s.mem (s.ea (at_ .esi i))).toNat = v

theorem Byt.of_only {s s' : State} {i v : Nat} {ds : List Reg} (h : Byt s i v) (ho : Only ds s s')
    (hesi : Reg.esi ∉ ds) : Byt s' i v := by
  have e : s'.ea (at_ .esi i) = s.ea (at_ .esi i) := by simp only [State.ea, at_, ho.gpr _ hesi]
  exact ⟨by rw [e, ho.rd, ho.wr]; exact h.in_, by rw [e, ho.mem]; exact h.val⟩

theorem Byt.lt {s : State} {i v : Nat} (h : Byt s i v) : v < 256 := by
  rw [← h.val]; exact (s.mem _).isLt

/-- `movzx d, byte [esi + i]`. -/
theorem wp_ldb {d : Reg} {i v : Nat} {is : List Instr} {s : State} {Q : State → Prop} (hb : Byt s i v)
    (k : ∀ s', Only [d] s s' → (s'.gpr d).toNat = v → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d (at_ .esi i) :: is)) s Q :=
  wp_movzx hb.in_ (k _ (Only.setReg s d _) (by simp only [State.setReg, ite_true]; rw [toNat_byte32, hb.val]))

theorem bySteps_spec (o : Nat) (x : Nat → Nat) :
    ∀ (j : Nat) (is : List Instr) (s : State) (P : State → Prop) (A : Nat),
      (∀ i < j, Byt s (o + i) (x i)) → (s.gpr .ebx).toNat = A → (A + 1) * 2 ^ (8 * j) ≤ 2 ^ 32 →
      (∀ s', Only [.eax, .ebx] s s' → (s'.gpr .ebx).toNat = A * 2 ^ (8 * j) + pk 8 x j →
        WP isa (.block is) s' P) →
      WP isa (.block (bySteps o j ++ is)) s P
  | 0, is, s, P, A, _, hA, _, k => k s (Only.refl _ _) (by simp [pk, hA])
  | j + 1, is, s, P, A, hc, hA, hb, k => by
    have hpj : 1 ≤ 2 ^ (8 * j) := Nat.one_le_two_pow
    have hsplit : 2 ^ (8 * (j + 1)) = 2 ^ 8 * 2 ^ (8 * j) := by
      rw [← Nat.pow_add]; congr 1; rw [Nat.mul_succ, Nat.add_comm]
    have hAl : A < 2 ^ 24 := by
      have : (A + 1) * 2 ^ 8 ≤ 2 ^ 32 := by
        refine Nat.le_trans ?_ hb
        rw [hsplit, ← Nat.mul_assoc]
        exact Nat.le_mul_of_pos_right _ hpj
      omega
    have hx := (hc j (by omega)).lt
    rw [bySteps, byteStep, List.append_assoc, List.cons_append]
    refine wp_ldb (hc j (by omega)) fun s₁ o₁ v₁ => ?_
    refine wp_ror (by decide) (by decide) fun s₂ o₂ e₂ => wp_addr fun s₃ o₃ e₃ => ?_
    have oo := (o₁.trans o₂).trans o₃
    have v₃ : (s₃.gpr .ebx).toNat = A * 2 ^ 8 + x j := by
      have r := ror_shl (d := 8) (A := A) (by decide) (by decide) (s₁.gpr .ebx)
        (by rw [o₁.gpr _ (by decide), hA]) hAl
      rw [e₃, BitVec.toNat_add, e₂, r, o₂.gpr .eax (by decide), v₁]
      omega
    refine bySteps_spec o x j is s₃ P _ (fun i hi => (hc i (by omega)).of_only oo (by decide)) v₃ ?_
      fun s₄ o₄ v₄ => k s₄ ((oo.trans o₄).mono fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with ((h | h) | h) | h | h <;> simp only [h, true_or, or_true]) ?_
    · have : A * 2 ^ 8 + x j + 1 ≤ (A + 1) * 2 ^ 8 := by rw [Nat.add_mul]; omega
      refine Nat.le_trans (Nat.mul_le_mul_right _ this) ?_
      rw [Nat.mul_assoc, ← hsplit]; exact hb
    · rw [v₄, pk, hsplit, Nat.add_mul, Nat.mul_assoc]
      omega

/-- `ldW o n` loads the `n + 1` bytes at `esi + o` into `ebx`, as the number whose base-2⁸ digits
they are. -/
theorem ldW_spec (o n : Nat) (hn : n ≤ 3) (x : Nat → Nat) (is : List Instr) (s : State) (P : State → Prop)
    (hc : ∀ i < n + 1, Byt s (o + i) (x i))
    (k : ∀ s', Only [.ebx, .eax, .ebx] s s' → (s'.gpr .ebx).toNat = pk 8 x (n + 1) → WP isa (.block is) s' P) :
    WP isa (.block (ldW o n ++ is)) s P := by
  rw [ldW, List.cons_append]
  refine wp_ldb (hc n (by omega)) fun s₁ o₁ v₁ => ?_
  have hx := (hc n (by omega)).lt
  refine bySteps_spec o x n is s₁ P _ (fun i hi => (hc i (by omega)).of_only o₁ (by decide)) v₁ ?_
    fun s₂ o₂ v₂ => k s₂ (o₁.trans o₂) ?_
  · have : 2 ^ (8 * n) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by omega)
    calc (x n + 1) * 2 ^ (8 * n) ≤ 2 ^ 8 * 2 ^ 24 := Nat.mul_le_mul (by omega) this
      _ = 2 ^ 32 := by decide
  · rw [v₂, pk]; omega

end VG.Proof.MlKem1024.X86
