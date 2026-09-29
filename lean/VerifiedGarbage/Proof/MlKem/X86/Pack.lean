import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Impl.MlKem.X86.Compress

/-!
# ML-KEM on x86 (32-bit): compressing and packing coefficients

Untrusted: everything here is checked by Lean. `compOp` computes the
compress formula of `Compress.lean` (`comp_spec`); `accStep` packs one more
compressed coefficient into `ebx` (`accStep_spec`), and `accSteps` packs
`j` of them, from `j - 1` down to 0 (`accSteps_spec`), as the number `pk`
whose base-`2ᵈ` digits they are.
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-- The compress formula, on the integer `a`. -/
def cf (d a : Nat) : Nat := (a * compressMul d + compressAdd) / 2 ^ 19 % 2 ^ d

theorem cf_lt (d a : Nat) : cf d a < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)

theorem cf_eq {d : Nat} (hd : d ∈ compressWidths) {a : Nat} (ha : a < q) :
    cf d a = compress d (ofNat a) := by
  rw [compress_eq hd, ofNat_of_lt ha, cf]

theorem cmul_eq (d : Nat) : cmul d = compressMul d := rfl

/-- `compOp d` computes `cf d a` in `eax` from `eax = a < q`, changing only `eax`, `edx` and the
flags. -/
theorem comp_spec {d : Nat} (hd : d ∈ compressWidths) (is : List Instr) (s : State) (P : State → Prop)
    {a : Nat} (ha : a < q) (h : (s.gpr .eax).toNat = a)
    (k : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = cf d a → WP isa (.block is) s' P) :
    WP isa (.block (compOp d ++ is)) s P := by
  have hd' : d < 32 := by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
  have hl := compress_arg_lt hd (ofNat a)
  rw [ofNat_of_lt ha] at hl
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [compOp, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, execMul, readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    Option.map_some, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · simp only [ite_true]
    rw [toNat_and_mask _ _ hd', toNat_shr]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h]
    have hm : cmul d < 2 ^ 32 := by
      rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
    rw [Nat.mod_eq_of_lt hm, show (262080 : BitVec 32).toNat = compressAdd from rfl, cmul_eq,
      Nat.mod_eq_of_lt (a := a * compressMul d) (by unfold compressAdd at hl; omega),
      Nat.mod_eq_of_lt (a := a * compressMul d + compressAdd) (by omega)]
    rfl

/-- Coefficient `i` from `esi`: at `[esi + 4i]`, readable, the integer `a < q`. -/
structure Coef (s : State) (i a : Nat) : Prop where
  in_ : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi (4 * i))) 4
  val : (s.mem.readW (s.ea (at_ .esi (4 * i))) 32).toNat = a
  lt : a < q

theorem Coef.of_only {s s' : State} {i a : Nat} {ds : List Reg} (h : Coef s i a) (ho : Only ds s s')
    (hesi : Reg.esi ∉ ds) : Coef s' i a := by
  have e : s'.ea (at_ .esi (4 * i)) = s.ea (at_ .esi (4 * i)) := by
    simp only [State.ea, at_, ho.gpr _ hesi]
  exact ⟨by rw [e, ho.rd, ho.wr]; exact h.in_, by rw [e, ho.mem]; exact h.val, h.lt⟩

/-- `mov eax, [esi + 4j]`, then `compOp d`. -/
theorem ldComp_spec {d : Nat} (hd : d ∈ compressWidths) (j : Nat) (is : List Instr) (s : State)
    (P : State → Prop) {a : Nat} (hc : Coef s j a)
    (k : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = cf d a → WP isa (.block is) s' P) :
    WP isa (.block (.mov .eax (.mem (at_ .esi (4 * j))) :: (compOp d ++ is))) s P :=
  wp_movm hc.in_ (comp_spec hd is _ P hc.lt (by simp only [State.setReg, ite_true]; exact hc.val)
    fun s' o v => k s' ⟨fun r hr => by
      rw [o.gpr r hr]; simp only [State.setReg]
      rw [ite_eq_right_iff.mpr fun (e : r = .eax) => absurd (e ▸ List.mem_cons_self ..) hr], o.mem, o.rd, o.wr⟩ v)

theorem ror_shl {A d : Nat} (hd0 : 0 < d) (hd : d < 32) (x : BitVec 32) (hx : x.toNat = A)
    (hA : A < 2 ^ (32 - d)) : (x.rotateRight (32 - d)).toNat = A * 2 ^ d := by
  rw [rotr_small x (by omega) (by omega) (by rw [hx]; exact hA), hx, show 32 - (32 - d) = d by omega]

theorem accStep_spec {d : Nat} (hd : d ∈ compressWidths) (j : Nat) (is : List Instr) (s : State)
    (P : State → Prop) {a A : Nat} (hc : Coef s j a) (hA : (s.gpr .ebx).toNat = A)
    (hAl : A < 2 ^ (32 - d))
    (k : ∀ s', Only [.eax, .edx, .ebx] s s' → (s'.gpr .ebx).toNat = A * 2 ^ d + cf d a →
      WP isa (.block is) s' P) :
    WP isa (.block (accStep d j ++ is)) s P := by
  have hd' : 0 < d ∧ d < 32 := by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
  rw [accStep, List.append_assoc, List.cons_append]
  refine ldComp_spec hd j _ s P hc fun s₁ o₁ v₁ => ?_
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    execShift, readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some, ite_true, ite_false,
    Option.some.injEq, exists_eq_left', show 1 ≤ 32 - d by omega, show 32 - d ≤ 31 by omega, and_self]
  refine k _ ⟨fun r hr => ?_, o₁.mem, o₁.rd, o₁.wr⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2, ite_false]
    exact o₁.gpr r (by simp [hr.1, hr.2.1])
  · simp only [ite_true]
    have hb : (s₁.gpr .ebx).toNat = A := by rw [o₁.gpr _ (by decide), hA]
    have hc' := cf_lt d a
    have hp : A * 2 ^ d + 2 ^ d ≤ 2 ^ 32 := by
      have := Nat.mul_le_mul_right (2 ^ d) (show A + 1 ≤ 2 ^ (32 - d) by omega)
      rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel (by omega)] at this
      exact this
    rw [BitVec.toNat_add, ror_shl hd'.1 hd'.2 _ hb hAl, v₁, Nat.mod_eq_of_lt (by omega)]

/-- `Σ_{i<j} cv i · 2^(d i)`: the number whose base-`2ᵈ` digits are `cv 0 … cv (j - 1)`. -/
def pk (d : Nat) (cv : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => pk d cv j + cv j * 2 ^ (d * j)

theorem accSteps_spec {d : Nat} (hd : d ∈ compressWidths) (a : Nat → Nat) :
    ∀ (j : Nat) (is : List Instr) (s : State) (P : State → Prop) (A : Nat),
      (∀ i < j, Coef s i (a i)) → (s.gpr .ebx).toNat = A → (A + 1) * 2 ^ (d * j) ≤ 2 ^ 32 →
      (∀ s', Only [.eax, .edx, .ebx] s s' →
        (s'.gpr .ebx).toNat = A * 2 ^ (d * j) + pk d (fun i => cf d (a i)) j → WP isa (.block is) s' P) →
      WP isa (.block (accSteps d j ++ is)) s P
  | 0, is, s, P, A, _, hA, _, k => k s (Only.refl _ _) (by simp [pk, hA])
  | j + 1, is, s, P, A, hc, hA, hb, k => by
    have hd' : 0 < d ∧ d < 32 := by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
    have hpj : 1 ≤ 2 ^ (d * j) := Nat.one_le_two_pow
    have hsplit : 2 ^ (d * (j + 1)) = 2 ^ d * 2 ^ (d * j) := by
      rw [← Nat.pow_add]; congr 1; rw [Nat.mul_succ, Nat.add_comm]
    have hAl : A < 2 ^ (32 - d) := by
      have h1 : (A + 1) * 2 ^ d ≤ 2 ^ (32 - d) * 2 ^ d := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
        refine Nat.le_trans ?_ hb
        rw [hsplit, ← Nat.mul_assoc]
        exact Nat.le_mul_of_pos_right _ hpj
      have := Nat.le_of_mul_le_mul_right h1 (Nat.two_pow_pos d)
      omega
    rw [accSteps, List.append_assoc]
    refine accStep_spec hd j _ s P (hc j (by omega)) hA hAl fun s₁ o₁ v₁ => ?_
    refine accSteps_spec hd a j is s₁ P _ (fun i hi => (hc i (by omega)).of_only o₁ (by decide)) v₁ ?_
      fun s₂ o₂ v₂ => k s₂ ((o₁.trans o₂).mono fun r hr => by
        rcases List.mem_append.mp hr with h | h <;> exact h) ?_
    · have hc' := cf_lt d (a j)
      have : A * 2 ^ d + cf d (a j) + 1 ≤ (A + 1) * 2 ^ d := by rw [Nat.add_mul]; omega
      refine Nat.le_trans (Nat.mul_le_mul_right _ this) ?_
      rw [Nat.mul_assoc, ← hsplit]; exact hb
    · rw [v₂, pk, hsplit, Nat.add_mul, Nat.mul_assoc]
      omega

theorem pk_congr {d : Nat} {cv cv' : Nat → Nat} : ∀ {j : Nat}, (∀ i < j, cv i = cv' i) →
    pk d cv j = pk d cv' j
  | 0, _ => rfl
  | j + 1, h => by rw [pk, pk, pk_congr (fun i hi => h i (by omega)), h j (by omega)]

theorem pk_lt {d : Nat} (cv : Nat → Nat) (h : ∀ i, cv i < 2 ^ d) : ∀ j, pk d cv j < 2 ^ (d * j)
  | 0 => by simp [pk]
  | j + 1 => by
    have ih := pk_lt cv h j
    have hc := h j
    have e : 2 ^ (d * (j + 1)) = 2 ^ d * 2 ^ (d * j) := by
      rw [← Nat.pow_add]; congr 1; rw [Nat.mul_succ, Nat.add_comm]
    rw [pk, e]
    have : cv j * 2 ^ (d * j) + 2 ^ (d * j) ≤ 2 ^ d * 2 ^ (d * j) := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hc
    omega

end VG.Proof.MlKem.X86
