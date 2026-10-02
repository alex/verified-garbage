import VerifiedGarbage.Proof.MlKem.X86.Pack
import VerifiedGarbage.Proof.MlKem.X86.Unpack
import VerifiedGarbage.Proof.MlKem.Compress1024
import VerifiedGarbage.Impl.MlKem1024.X86.Compress

/-!
# ML-KEM-1024 on x86 (32-bit): compressing and packing coefficients

As `Proof/MlKem/X86/Pack.lean`, for the widths of ML-KEM-1024: `cOp` computes
the compress formula of `Compress1024.lean` (`cOp_spec`); `accS` packs one more
compressed coefficient into `ebx` (`accS_spec`), and `accSs d o j` packs `j` of
them, from `o + j - 1` down to `o` (`accSs_spec`), as the number `pk` whose
base-`2ᵈ` digits they are.
-/

namespace VG.Proof.MlKem1024.X86

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

/-- The compress formula of ML-KEM-1024, on the integer `a`. -/
def cf (d a : Nat) : Nat := (a * compressMul1024 d + compressAdd1024) / 2 ^ 19 % 2 ^ d

theorem cf_lt (d a : Nat) : cf d a < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)

theorem cf_eq {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) {a : Nat} (ha : a < q) :
    cf d a = compress d (ofNat a) := by
  rw [compress1024_eq hd, ofNat_of_lt ha, cf]

theorem cmul_eq (d : Nat) : cmul1024 d = compressMul1024 d := rfl

/-- `cOp d` computes `cf d a` in `eax` from `eax = a < q`, changing only `eax`, `edx` and the
flags. -/
theorem cOp_spec {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) (is : List Instr) (s : State)
    (P : State → Prop) {a : Nat} (ha : a < q) (h : (s.gpr .eax).toNat = a)
    (k : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = cf d a → WP isa (.block is) s' P) :
    WP isa (.block (cOp d ++ is)) s P := by
  have hd' : d < 32 := by rcases mem_compressWidths1024 hd with rfl | rfl <;> decide
  have hl := compress1024_arg_lt hd (ofNat a)
  rw [ofNat_of_lt ha] at hl
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [cOp, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, execMul, readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    Option.map_some, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · simp only [ite_true]
    rw [toNat_and_mask _ _ hd', toNat_shr]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h]
    have hm : cmul1024 d < 2 ^ 32 := by
      rcases mem_compressWidths1024 hd with rfl | rfl <;> decide
    rw [Nat.mod_eq_of_lt hm, show (261888 : BitVec 32).toNat = compressAdd1024 from rfl, cmul_eq,
      Nat.mod_eq_of_lt (a := a * compressMul1024 d) (by unfold compressAdd1024 at hl; omega),
      Nat.mod_eq_of_lt (a := a * compressMul1024 d + compressAdd1024) (by omega)]
    rfl

/-- `mov eax, [esi + 4j]`, then `cOp d`. -/
theorem ldC_spec {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) (j : Nat) (is : List Instr)
    (s : State) (P : State → Prop) {a : Nat} (hc : Coef s j a)
    (k : ∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = cf d a → WP isa (.block is) s' P) :
    WP isa (.block (ldC d j ++ is)) s P :=
  wp_movm hc.in_ (cOp_spec hd is _ P hc.lt (by simp only [State.setReg, ite_true]; exact hc.val)
    fun s' o v => k s' ⟨fun r hr => by
      rw [o.gpr r hr]; simp only [State.setReg]
      rw [ite_eq_right_iff.mpr fun (e : r = .eax) => absurd (e ▸ List.mem_cons_self ..) hr], o.mem, o.rd, o.wr⟩ v)

theorem accS_spec {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) (o j : Nat) (is : List Instr)
    (s : State) (P : State → Prop) {a A : Nat} (hc : Coef s (o + j) a) (hA : (s.gpr .ebx).toNat = A)
    (hAl : A < 2 ^ (32 - d))
    (k : ∀ s', Only [.eax, .edx, .ebx] s s' → (s'.gpr .ebx).toNat = A * 2 ^ d + cf d a →
      WP isa (.block is) s' P) :
    WP isa (.block (accS d o j ++ is)) s P := by
  have hd' : 0 < d ∧ d < 32 := by rcases mem_compressWidths1024 hd with rfl | rfl <;> decide
  rw [accS, List.append_assoc]
  refine ldC_spec hd (o + j) _ s P hc fun s₁ o₁ v₁ => ?_
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

theorem accSs_spec {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) (o : Nat) (a : Nat → Nat) :
    ∀ (j : Nat) (is : List Instr) (s : State) (P : State → Prop) (A : Nat),
      (∀ i < j, Coef s (o + i) (a i)) → (s.gpr .ebx).toNat = A → (A + 1) * 2 ^ (d * j) ≤ 2 ^ 32 →
      (∀ s', Only [.eax, .edx, .ebx] s s' →
        (s'.gpr .ebx).toNat = A * 2 ^ (d * j) + pk d (fun i => cf d (a i)) j → WP isa (.block is) s' P) →
      WP isa (.block (accSs d o j ++ is)) s P
  | 0, is, s, P, A, _, hA, _, k => k s (Only.refl _ _) (by simp [pk, hA])
  | j + 1, is, s, P, A, hc, hA, hb, k => by
    have hd' : 0 < d ∧ d < 32 := by rcases mem_compressWidths1024 hd with rfl | rfl <;> decide
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
    rw [accSs, List.append_assoc]
    refine accS_spec hd o j _ s P (hc j (by omega)) hA hAl fun s₁ o₁ v₁ => ?_
    refine accSs_spec hd o a j is s₁ P _ (fun i hi => (hc i (by omega)).of_only o₁ (by decide)) v₁ ?_
      fun s₂ o₂ v₂ => k s₂ ((o₁.trans o₂).mono fun r hr => by
        rcases List.mem_append.mp hr with h | h <;> exact h) ?_
    · have hc' := cf_lt d (a j)
      have : A * 2 ^ d + cf d (a j) + 1 ≤ (A + 1) * 2 ^ d := by rw [Nat.add_mul]; omega
      refine Nat.le_trans (Nat.mul_le_mul_right _ this) ?_
      rw [Nat.mul_assoc, ← hsplit]; exact hb
    · rw [v₂, pk, hsplit, Nat.add_mul, Nat.mul_assoc]
      omega

/-! ## Single instructions -/

/-- `ror d, n` -/
theorem wp_ror {d : Reg} {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) {is : List Instr} {s : State}
    {Q : State → Prop} (k : ∀ s', Only [d] s s' → s'.gpr d = (s.gpr d).rotateRight n → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .ror d n :: is)) s Q := by
  refine wp_cons (s' := (s.setFlags (some ((s.gpr d).rotateRight n).msb)
    (if n = 1 then some (((s.gpr d).rotateRight n).msb ^^ ((s.gpr d).rotateRight n).getMsbD 1) else none)
    s.zf s.sf).setReg d ((s.gpr d).rotateRight n)) ?_ (k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_)
  · simp only [exec, execShift, h1, h2, and_self, ite_true]
  · simp only [State.setReg]
    rw [ite_eq_right_iff.mpr fun (e : r = d) => absurd (e ▸ List.mem_singleton_self d) hr]
    rfl
  · simp [State.setReg]

/-- `add d, r` -/
theorem wp_addr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d + s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q := by
  refine wp_cons (s' := (arithFlags s (s.gpr d + s.gpr r) (decide (2 ^ 32 ≤ (s.gpr d).toNat + (s.gpr r).toNat))
      (addOverflow (s.gpr d) (s.gpr r) (s.gpr d + s.gpr r))).setReg d (s.gpr d + s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some]) (k _ ⟨fun x hx => ?_, rfl, rfl, rfl⟩ ?_)
  · simp only [State.setReg]
    rw [ite_eq_right_iff.mpr fun (e : x = d) => absurd (e ▸ List.mem_singleton_self d) hx]
    rfl
  · simp [State.setReg]

/-- `mov d, r` -/
theorem wp_mov {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  wp_movr (k _ (Only.setReg s d _) (by simp [State.setReg]))

/-- `mov byte [b + disp], r` -/
theorem wp_st8 {b : Reg} {r : Reg8} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions s.wr (s.ea (at_ b disp)) 1)
    (k : WP isa (.block is) { s with mem := s.mem.writeW (s.ea (at_ b disp)) ((s.gpr r.reg).setWidth 8) } Q) :
    WP isa (.block (.store8 (at_ b disp) r :: is)) s Q :=
  wp_cons (by simp only [exec, State.store8, hin, ite_true]) k

end VG.Proof.MlKem1024.X86
