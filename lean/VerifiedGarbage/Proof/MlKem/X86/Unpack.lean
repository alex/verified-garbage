import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Impl.MlKem.X86.Compress

/-!
# ML-KEM on x86 (32-bit): unpacking and decompressing coefficients

`decompOp` computes the decompress formula of `Compress.lean` (`decomp_spec`);
`unpackStep d j` writes coefficient `j` from field `j` of `ebx`
(`unpackStep_spec`), and `unpackSteps d k` the first `k` of them
(`unpackSteps_spec`).
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-- The decompress formula, on the integer `y`. -/
def dv (d y : Nat) : Nat := (q * y + 2 ^ (d - 1)) / 2 ^ d

/-- `s'` is `s` but for the registers `ds`, the flags and memory. -/
structure Regs (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Regs.of_only {ds : List Reg} {s s' : State} (h : Only ds s s') : Regs ds s s' := ⟨h.gpr, h.rd, h.wr⟩

theorem Regs.trans {ds es : List Reg} {s₁ s₂ s₃ : State} (h₁ : Regs ds s₁ s₂) (h₂ : Regs es s₂ s₃) :
    Regs (ds ++ es) s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1], h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Regs.mono {ds es : List Reg} {s s' : State} (h : Regs ds s s') (he : ∀ r ∈ ds, r ∈ es) :
    Regs es s s' := ⟨fun r hr => h.gpr r fun h' => hr (he r h'), h.rd, h.wr⟩

/-- `decompOp d` computes `dv d y` in `eax` from `eax = y < 2ᵈ`, changing only `eax`, `edx` and
the flags. -/
theorem decomp_spec {d : Nat} (hd : d ∈ compressWidths) (is : List Instr) (s : State) (P : State → Prop)
    {y : Nat} (hy : y < 2 ^ d) (h : (s.gpr .eax).toNat = y)
    (k : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = dv d y → WP isa (.block is) s' P) :
    WP isa (.block (decompOp d ++ is)) s P := by
  have hd' : 1 ≤ d ∧ d ≤ 31 ∧ y < 1024 := by
    rcases mem_compressWidths hd with rfl | rfl | rfl <;> refine ⟨by decide, by decide, ?_⟩ <;> omega
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [decompOp, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, execMul, readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    Option.map_some, ite_true, ite_false, Option.some.injEq, exists_eq_left', hd'.1, hd'.2.1, and_self]
  refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · simp only [ite_true]
    have hp : 2 ^ (d - 1) ≤ 512 := by
      rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
    rw [toNat_shr]
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, h]
    rw [show (3329 : BitVec 32).toNat = 3329 from rfl, Nat.mod_eq_of_lt (a := y * 3329) (by omega), Nat.mod_eq_of_lt (a := 2 ^ (d - 1)) (by omega),
      Nat.mod_eq_of_lt (by omega), dv, q_eq, Nat.mul_comm y]

theorem shrFrom_spec (sh : Nat) (hsh : sh ≤ 31) (is : List Instr) (s : State) (P : State → Prop)
    (k : ∀ s', Only [.eax] s s' → s'.gpr .eax = s.gpr .ebx >>> sh → WP isa (.block is) s' P) :
    WP isa (.block (shrFrom sh ++ is)) s P := by
  unfold shrFrom
  refine wp_movr ?_
  by_cases h0 : sh = 0
  · subst h0
    simp only [ite_true]
    refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ (by simp [State.setReg])
    simp only [State.setReg]
    rw [ite_eq_right_iff.mpr fun (e : r = .eax) => absurd (e ▸ List.mem_singleton_self _) hr]
  · simp only [h0, ite_false]
    refine wp_shr (by omega) hsh fun s' o v => k s' ⟨fun r hr => ?_, o.mem, o.rd, o.wr⟩ ?_
    · rw [o.gpr r hr]; simp only [State.setReg]
      rw [ite_eq_right_iff.mpr fun (e : r = .eax) => absurd (e ▸ List.mem_singleton_self _) hr]
    · rw [v]; simp [State.setReg]

/-- The value of field `j` of `B`, decompressed. -/
def dfield (d B j : Nat) : Nat := dv d (B / 2 ^ (d * j) % 2 ^ d)

/-- `unpackStep d j` writes `dfield d B j` to `[edi + 4j]`, from `ebx = B`. -/
theorem unpackStep_spec {d : Nat} (hd : d ∈ compressWidths) (j : Nat) (hj : d * j ≤ 31)
    (is : List Instr) (s : State) (P : State → Prop) {B : Nat} (hB : (s.gpr .ebx).toNat = B)
    (hin : InRegions s.wr (s.ea (at_ .edi (4 * j))) 4)
    (k : ∀ s', Regs [.eax, .edx] s s' →
      s'.mem = s.mem.writeW (s.ea (at_ .edi (4 * j))) (BitVec.ofNat 32 (dfield d B j)) →
      WP isa (.block is) s' P) :
    WP isa (.block (unpackStep d j ++ is)) s P := by
  have hd' : d < 32 := by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
  rw [unpackStep, List.append_assoc]
  refine shrFrom_spec _ hj _ s P fun s₁ o₁ v₁ => ?_
  rw [List.append_assoc, List.cons_append]
  refine wp_cons (s' := (s₁.setFlags (some false) (some false)
    (some (s₁.gpr .eax &&& BitVec.ofNat 32 (2 ^ d - 1) == 0))
    (some (s₁.gpr .eax &&& BitVec.ofNat 32 (2 ^ d - 1)).msb)).setReg .eax
    (s₁.gpr .eax &&& BitVec.ofNat 32 (2 ^ d - 1))) (by simp only [exec, execAlu, readSrc,
      Option.bind_some, arithFlags]) ?_
  have hy : ((s₁.gpr .eax &&& BitVec.ofNat 32 (2 ^ d - 1))).toNat = B / 2 ^ (d * j) % 2 ^ d := by
    rw [toNat_and_mask _ _ hd', v₁, toNat_shr, hB]
  refine decomp_spec hd _ _ P (Nat.mod_lt _ (Nat.two_pow_pos d)) (by simpa [State.setReg] using hy)
    fun s₂ o₂ v₂ => ?_
  have edi₂ : s₂.gpr .edi = s.gpr .edi := by
    rw [o₂.gpr .edi (by decide)]
    simp only [State.setReg, State.setFlags, show Reg.edi ≠ Reg.eax by decide, ite_false]
    exact o₁.gpr .edi (by decide)
  have mem₂ : s₂.mem = s.mem := by rw [o₂.mem]; exact o₁.mem
  have wr₂ : s₂.wr = s.wr := by rw [o₂.wr]; exact o₁.wr
  have rd₂ : s₂.rd = s.rd := by rw [o₂.rd]; exact o₁.rd
  have ea₂ : s₂.ea (at_ .edi (4 * j)) = s.ea (at_ .edi (4 * j)) := by simp only [State.ea, at_, edi₂]
  refine wp_store (by rw [ea₂, wr₂]; exact hin) ?_
  refine k _ ⟨fun r hr => ?_, rd₂, wr₂⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    show s₂.gpr r = s.gpr r
    rw [o₂.gpr r (by simp [hr.1, hr.2])]
    simp only [State.setReg, State.setFlags, hr.1, ite_false]
    exact o₁.gpr r (by simp [hr.1])
  · show s₂.mem.writeW (s₂.ea (at_ .edi (4 * j))) (s₂.gpr .eax) = _
    rw [ea₂, mem₂, eq_ofNat_of_toNat v₂, dfield]

theorem dk_le {d k : Nat} (hd : d ∈ compressWidths) (h : d * (k + 1) ≤ 32) : d * k ≤ 31 := by
  rcases mem_compressWidths hd with rfl | rfl | rfl <;> omega

/-- `unpackSteps d k` writes `dfield d B j` to `[edi + 4j]` for `j < k`, from `ebx = B`, where
`edi` is at coefficient `i₀` of the polynomial at `p`. -/
theorem unpackSteps_spec {d : Nat} (hd : d ∈ compressWidths) {p : Addr} {i₀ B : Nat} :
    ∀ (k : Nat) (is : List Instr) (s : State) (P : State → Prop), d * k ≤ 32 → i₀ + k ≤ 256 →
      (s.gpr .ebx).toNat = B →
      (∀ j < k, s.ea (at_ .edi (4 * j)) = coeffAddr p (i₀ + j)) →
      (∀ j < k, InRegions s.wr (coeffAddr p (i₀ + j)) 4) →
      (∀ s', Regs [.eax, .edx] s s' → Frame [polyRegion p] s.mem s'.mem →
        (∀ i < 256, coeffAt s'.mem p i =
          if i₀ ≤ i ∧ i < i₀ + k then BitVec.ofNat 32 (dfield d B (i - i₀)) else coeffAt s.mem p i) →
        WP isa (.block is) s' P) →
      WP isa (.block (unpackSteps d k ++ is)) s P
  | 0, is, s, P, _, _, _, _, _, k => k s ⟨fun _ _ => rfl, rfl, rfl⟩ (Frame.refl _ _) fun i _ => by
      rw [ite_eq_right_iff.mpr fun h => absurd h.2 (by omega)]
  | k + 1, is, s, P, hdk, hik, hB, hea, hin, kk => by
    have hdk' : d * k ≤ 31 := dk_le hd hdk
    rw [unpackSteps, List.append_assoc]
    refine unpackSteps_spec hd k _ s P (by omega) (by omega) hB (fun j hj => hea j (by omega))
      (fun j hj => hin j (by omega)) fun s₁ o₁ f₁ c₁ => ?_
    have ea₁ : s₁.ea (at_ .edi (4 * k)) = coeffAddr p (i₀ + k) := by
      rw [← hea k (by omega)]; simp only [State.ea, at_, o₁.gpr _ (show Reg.edi ∉ [Reg.eax, .edx] by decide)]
    refine unpackStep_spec hd k hdk' is s₁ P (by rw [o₁.gpr _ (by decide), hB])
      (by rw [ea₁, o₁.wr]; exact hin k (by omega)) fun s₂ o₂ m₂ => ?_
    have hk' : i₀ + k < n := by rw [n_eq]; omega
    refine kk s₂ ((o₁.trans o₂).mono fun r hr => by
        rcases List.mem_append.mp hr with h | h <;> exact h)
      (by rw [m₂, ea₁]; exact f₁.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk'))
      fun i hi => ?_
    rw [m₂, ea₁, coeffAt_writeW _ _ (show i < n by rw [n_eq]; exact hi) hk', c₁ i hi]
    by_cases e : i₀ + k = i
    · subst e
      rw [ite_eq_left rfl, ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
    · rw [ite_eq_right e]
      by_cases hr : i₀ ≤ i ∧ i < i₀ + k
      · rw [ite_eq_left hr, ite_eq_left ⟨hr.1, by omega⟩]
      · rw [ite_eq_right hr, ite_eq_right (fun h => hr ⟨h.1, by omega⟩)]

theorem dv_lt {d : Nat} (hd : d ∈ compressWidths) {y : Nat} (hy : y < 2 ^ d) : dv d y < q :=
  (decompress_val hd hy).2

theorem dv_eq {d : Nat} (hd : d ∈ compressWidths) {y : Nat} (hy : y < 2 ^ d) :
    dv d y = (decompress d y).val := (decompress_val hd hy).1.symm

end VG.Proof.MlKem.X86
