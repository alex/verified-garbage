import VerifiedGarbage.Proof.MlDsa.X86.Arith.AddSub
import VerifiedGarbage.Impl.MlDsa.X86.Arith.Mul

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

`mulHead` leaves `f[i] · g[i] mod q` in `ebx` (`head_spec`): two Montgomery
reductions, the second of the first times `2⁶⁴ mod q` (`mont_mont_R2`). The
loop over the coefficients is proven once for both functions (`MulInv`,
`step`), with the value `V a b c` of coefficient `i` from those of `f`, `g`
and `h`.
-/

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_ leaf)
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86 (Only wp_cons wp_movm wp_movr wp_mul toNat_ofNat32 eq_ofNat_of_toNat E0 P0 P0_esp
  P0_wr frameR retR LeafPost LeafEnd Piece ea_add ptr_next cnt_next cnt_ne execMul_other satState)

theorem mulHead_eq (is : List Instr) : mulHead ++ is =
    .mov .eax (.mem (at_ .esi 0)) :: .mov .edx (.mem (at_ .edi 0)) :: .mul .edx :: (mredRaw .ebx ++
      (.mov .eax (.reg .ebx) :: .mov .edx (.imm r2Imm) :: .mul .edx :: (mred .ebx ++ is))) := by
  simp only [mulHead, List.cons_append, List.nil_append, List.append_assoc]

theorem r2Imm_toNat : r2Imm.toNat = 2 ^ 64 % q := rfl

/-- `mulHead` leaves `a · b mod q` in `ebx` from `[esi] = a` and `[edi] = b`,
changing only `eax`, `edx`, `ebx` and the flags. -/
theorem head_spec (is : List Instr) (s : State) (P : State → Prop) {a b : Nat} (ha : a < q) (hb : b < q)
    (hia : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 4) (hva : (s.mem.readW (s.ea (at_ .esi 0)) 32).toNat = a)
    (hib : InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 4) (hvb : (s.mem.readW (s.ea (at_ .edi 0)) 32).toNat = b)
    (k : ∀ s', Only [.eax, .edx, .ebx] s s' → (s'.gpr .ebx).toNat = a * b % q → WP isa (.block is) s' P) :
    WP isa (.block (mulHead ++ is)) s P := by
  rw [mulHead_eq]
  refine wp_movm hia (wp_movm ?_ (wp_mul ?_))
  · simpa only [State.ea, at_, State.setReg, show Reg.edi ≠ Reg.eax by decide, ite_false] using hib
  set s₁ := (s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32)).setReg .edx
    ((s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32)).mem.readW
      ((s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32)).ea (at_ .edi 0)) 32) with hs₁
  have e₁ : ((execMul .edx s₁).gpr .edx).toNat * 2 ^ 32 + ((execMul .edx s₁).gpr .eax).toNat = a * b := by
    rw [execMul_pair]
    simp only [hs₁, State.setReg, ite_true, ite_false, show Reg.eax ≠ Reg.edx by decide, State.ea, at_,
      show Reg.edi ≠ Reg.eax by decide]
    simp only [State.ea, at_] at hva hvb
    rw [hva, hvb]
  have hab : a * b < q * 2 ^ 32 := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt ha hb) (by decide)
  refine mredRaw_spec (by decide) (by decide) _ _ P e₁ hab fun s₂ o₂ v₂ => ?_
  refine wp_movr (wp_movi (wp_mul ?_))
  have ht := mont_lt hab
  have e₂ : ((execMul .edx ((s₂.setReg .eax (s₂.gpr .ebx)).setReg .edx r2Imm)).gpr .edx).toNat * 2 ^ 32 +
      ((execMul .edx ((s₂.setReg .eax (s₂.gpr .ebx)).setReg .edx r2Imm)).gpr .eax).toNat =
      mont (a * b) * (2 ^ 64 % q) := by
    rw [execMul_pair]
    simp only [State.setReg, ite_true, ite_false, show Reg.eax ≠ Reg.edx by decide]
    rw [v₂, r2Imm_toNat]
  have hlt : mont (a * b) * (2 ^ 64 % q) < q * 2 ^ 32 := by
    have : 2 ^ 64 % q < q := Nat.mod_lt _ (by decide)
    have := Nat.mul_lt_mul_of_lt_of_lt ht this
    rw [q_eq] at this ⊢; omega
  refine mred_spec (by decide) (by decide) _ _ P e₂ hlt fun s₃ o₃ v₃ => k s₃ ⟨fun r hr => ?_, ?_, ?_, ?_⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [o₃.gpr r (by simp [hr.1, hr.2.1, hr.2.2]), execMul_other _ _ hr.1 hr.2.1]
    simp only [State.setReg, hr.1, hr.2.1, ite_false]
    rw [o₂.gpr r (by simp [hr.1, hr.2.1, hr.2.2]), execMul_other _ _ hr.1 hr.2.1]
    simp [hs₁, State.setReg, hr.1, hr.2.1]
  · rw [o₃.mem]; simp only [execMul, State.setReg, State.setFlags]; rw [o₂.mem]; rfl
  · rw [o₃.rd]; simp only [execMul, State.setReg, State.setFlags]; rw [o₂.rd]; rfl
  · rw [o₃.wr]; simp only [execMul, State.setReg, State.setFlags]; rw [o₂.wr]; rfl
  · rw [v₃, mont_mont_R2]

/-! ## The bodies -/

/-- The arithmetic of the body of `multiplyNTT` (`acc = false`) or
`multiplyAddNTT` (`true`): `ebx ← V a b c` from `[esi] = a`, `[edi] = b` and
`[ebp] = c` (reduced if `acc`), changing only `eax`, `edx`, `ebx` and the
flags. -/
def CoreSpec (core : List Instr) (acc : Bool) (V : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (is : List Instr) (s : State) (P : State → Prop) (a b c : Nat), a < q → b < q → (acc = true → c < q) →
    InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 4 → (s.mem.readW (s.ea (at_ .esi 0)) 32).toNat = a →
    InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 4 → (s.mem.readW (s.ea (at_ .edi 0)) 32).toNat = b →
    InRegions (s.rd ++ s.wr) (s.ea (at_ .ebp 0)) 4 → (s.mem.readW (s.ea (at_ .ebp 0)) 32).toNat = c →
    (∀ s', Only [.eax, .edx, .ebx] s s' → (s'.gpr .ebx).toNat = V a b c → WP isa (.block is) s' P) →
    WP isa (.block (core ++ is)) s P

/-- The value of `multiplyNTT`. -/
def mulV (a b _c : Nat) : Nat := a * b % q

/-- The value of `multiplyAddNTT`. -/
def mulAddV (a b c : Nat) : Nat := (a * b % q + c) % q

theorem mul_core : CoreSpec mulHead false mulV :=
  fun is s P _ _ _ ha hb _ hia hva hib hvb _ _ k => head_spec is s P ha hb hia hva hib hvb k

/-- `mulHead`, then `h[i]` added. -/
def mulAddCore : List Instr := mulHead ++ .alu .add .ebx (.mem (at_ .ebp 0)) :: csubQ .ebx .edx

theorem mulAdd_core : CoreSpec mulAddCore true mulAddV := by
  intro is s P a b c ha hb hc hia hva hib hvb hic hvc k
  rw [mulAddCore, List.append_assoc]
  refine head_spec _ s P ha hb hia hva hib hvb fun s₁ o₁ v₁ => ?_
  have hc' := hc rfl
  have hic' : InRegions (s₁.rd ++ s₁.wr) ((s₁.gpr .ebp + BitVec.ofNat 32 0).setWidth 64) 4 := by
    rw [o₁.rd, o₁.wr, o₁.gpr .ebp (by decide)]; exact hic
  have hvc' : (s₁.mem.readW ((s₁.gpr .ebp + BitVec.ofNat 32 0).setWidth 64) 32).toNat = c := by
    rw [o₁.mem, o₁.gpr .ebp (by decide)]; exact hvc
  set C := s₁.mem.readW ((s₁.gpr .ebp + BitVec.ofNat 32 0).setWidth 64) 32 with hC
  rw [List.cons_append]
  refine wp_cons (s' := (arithFlags s₁ (s₁.gpr .ebx + C) (2 ^ 32 ≤ (s₁.gpr .ebx).toNat + C.toNat)
    (addOverflow (s₁.gpr .ebx) C (s₁.gpr .ebx + C))).setReg .ebx (s₁.gpr .ebx + C))
    (by simp only [exec, execAlu, readSrc, State.ea, at_, State.load32, hic', ite_true, Option.bind_some]; rfl) ?_
  have hlt := Nat.mod_lt (a * b) (show q > 0 by decide)
  have e : (s₁.gpr .ebx + C).toNat = a * b % q + c := by
    rw [BitVec.toNat_add, v₁, hvc', Nat.mod_eq_of_lt (by rw [q_eq] at hlt hc' ⊢; omega)]
  refine csubQ_spec (by decide) is _ P (by simp only [State.setReg, ite_true]; rw [e]; rw [q_eq] at hlt hc' ⊢; omega)
    fun s' o v => k s' ((o₁.trans (show Only [.ebx, .edx] s₁ s' from ⟨fun r hr => ?_, o.mem, o.rd, o.wr⟩)).mono
      fun r hr => ?_) ?_
  · rw [o.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [State.setReg, arithFlags, State.setFlags, hr.1]
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (e | e | e) | (e | e) <;> simp [e]
  · rw [v]; simp only [State.setReg, ite_true]; rw [e]; rfl

theorem mulBody_eq : mulBody = mulHead ++ mulTail := rfl

theorem mulAddBody_eq : mulAddBody = mulAddCore ++ mulTail := by
  simp only [mulAddBody, mulAddCore, List.append_assoc, List.cons_append]

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev hP : BitVec 32 := arg s₀ 0
abbrev fP' : BitVec 32 := arg s₀ 1
abbrev gP' : BitVec 32 := arg s₀ 2
abbrev hA : Addr := (hP s₀).setWidth 64
abbrev fA' : Addr := (fP' s₀).setWidth 64
abbrev gA' : Addr := (gP' s₀).setWidth 64
abbrev aR3 : Region := ⟨argAddr s₀ 0, 12⟩
end

/-- The precondition of both functions: `h` is reduced if `acc`. -/
structure MulPre (acc : Bool) (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 12 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (fA' s₀), polyRegion (gA' s₀)]
  wr : s₀.wr = [polyRegion (hA s₀), aR3 s₀]
  h_f : (polyRegion (hA s₀)).Disjoint (polyRegion (fA' s₀))
  h_g : (polyRegion (hA s₀)).Disjoint (polyRegion (gA' s₀))
  h_a : (polyRegion (hA s₀)).Disjoint (aR3 s₀)
  f_a : (polyRegion (fA' s₀)).Disjoint (aR3 s₀)
  g_a : (polyRegion (gA' s₀)).Disjoint (aR3 s₀)
  ret_h : (retR s₀).Disjoint (polyRegion (hA s₀))
  ret_f : (retR s₀).Disjoint (polyRegion (fA' s₀))
  ret_g : (retR s₀).Disjoint (polyRegion (gA' s₀))
  ret_a : (retR s₀).Disjoint (aR3 s₀)
  stk_h : (stkR s₀).Disjoint (polyRegion (hA s₀))
  stk_f : (stkR s₀).Disjoint (polyRegion (fA' s₀))
  stk_g : (stkR s₀).Disjoint (polyRegion (gA' s₀))
  stk_a : (stkR s₀).Disjoint (aR3 s₀)
  h_fit : (hP s₀).toNat + 1024 ≤ 2 ^ 32
  f_fit : (fP' s₀).toNat + 1024 ≤ 2 ^ 32
  g_fit : (gP' s₀).toNat + 1024 ≤ 2 ^ 32
  h_red : acc = true → Reduced s₀.mem (hA s₀)
  f_red : Reduced s₀.mem (fA' s₀)
  g_red : Reduced s₀.mem (gA' s₀)

theorem MulPre.of_mul {s₀ : State} (h : (mulContract X86.abi 16).pre s₀) : MulPre false s₀ := by
  sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    fun e => absurd e (by decide), h21, h22⟩

theorem MulPre.of_mulAdd {s₀ : State} (h : (mulAddContract X86.abi 16).pre s₀) : MulPre true s₀ := by
  sig_pre [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    fun _ => h21, h22, h23⟩

/-! ## The loop -/

/-- The new value of coefficient `i`. -/
def newM (V : Nat → Nat → Nat → Nat) (s₀ : State) (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (V (coeffAt s₀.mem (fA' s₀) i).toNat (coeffAt s₀.mem (gA' s₀) i).toNat
    (coeffAt s₀.mem (hA s₀) i).toNat)

/-- After `k` coefficients. -/
structure MulInv (V : Nat → Nat → Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  ebp : s.gpr .ebp = hP s₀ + BitVec.ofNat 32 (4 * k)
  esi : s.gpr .esi = fP' s₀ + BitVec.ofNat 32 (4 * k)
  edi : s.gpr .edi = gP' s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  frame : Frame [polyRegion (hA s₀)] (P0 s₀).mem s.mem
  h : ∀ i < 256, coeffAt s.mem (hA s₀) i = if i < k then newM V s₀ i else coeffAt s₀.mem (hA s₀) i

namespace MulPre
variable {acc : Bool} {s₀ : State} (hp : MulPre acc s₀)
include hp

theorem in_h {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions s.wr (coeffAddr (hA s₀) k) 4 := by
  rw [hw, P0_wr, hp.wr]
  exact ⟨polyRegion (hA s₀), by simp, coeff_contains _ hk⟩

theorem in_h' {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (hA s₀) k) 4 :=
  let ⟨r, h, c⟩ := hp.in_h hw hk; ⟨r, List.mem_append_right _ h, c⟩

theorem in_f {s : State} (hr : s.rd = (P0 s₀).rd) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (fA' s₀) k) 4 := by
  rw [hr, pushed_rd, hp.rd]
  exact ⟨polyRegion (fA' s₀), by simp, coeff_contains _ hk⟩

theorem in_g {s : State} (hr : s.rd = (P0 s₀).rd) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (gA' s₀) k) 4 := by
  rw [hr, pushed_rd, hp.rd]
  exact ⟨polyRegion (gA' s₀), by simp, coeff_contains _ hk⟩

/-- `f` and `g` are never written. -/
theorem f_keep {s : State} (hf : Frame [polyRegion (hA s₀)] (P0 s₀).mem s.mem) {i : Nat} (hi : i < 256) :
    coeffAt s.mem (fA' s₀) i = coeffAt s₀.mem (fA' s₀) i := by
  rw [coeffAt_congr (m := s₀.mem) (m' := s.mem) (fun j hj => ?_) hi]
  rw [hf.bytes (R := polyRegion (fA' s₀)) (by simpa using hp.h_f.symm) (polyLen _) hj,
    (P0_mem hp.sp).bytes (R := polyRegion (fA' s₀)) (by simpa [← stk_eq hp.sp] using hp.stk_f.symm)
      (polyLen _) hj]

theorem g_keep {s : State} (hf : Frame [polyRegion (hA s₀)] (P0 s₀).mem s.mem) {i : Nat} (hi : i < 256) :
    coeffAt s.mem (gA' s₀) i = coeffAt s₀.mem (gA' s₀) i := by
  rw [coeffAt_congr (m := s₀.mem) (m' := s.mem) (fun j hj => ?_) hi]
  rw [hf.bytes (R := polyRegion (gA' s₀)) (by simpa using hp.h_g.symm) (polyLen _) hj,
    (P0_mem hp.sp).bytes (R := polyRegion (gA' s₀)) (by simpa [← stk_eq hp.sp] using hp.stk_g.symm)
      (polyLen _) hj]

theorem h_P0 {i : Nat} (hi : i < 256) : coeffAt (P0 s₀).mem (hA s₀) i = coeffAt s₀.mem (hA s₀) i :=
  coeffAt_congr (fun j hj => (P0_mem hp.sp).bytes (R := polyRegion (hA s₀))
    (by simpa [← stk_eq hp.sp] using hp.stk_h.symm) (polyLen _) hj) hi

end MulPre

theorem mul_step {core : List Instr} {acc : Bool} {V : Nat → Nat → Nat → Nat} (hc : CoreSpec core acc V)
    {s₀ : State} (hp : MulPre acc s₀) {k : Nat} (hk : k < 256) {s : State} (h : MulInv V s₀ k s) :
    WP isa (.block (core ++ mulTail)) s fun s' =>
      MulInv V s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < n := hk
  have eh : s.ea (at_ .ebp 0) = coeffAddr (hA s₀) k := by
    rw [State.ea, at_, h.ebp]; exact ea_ptr hp.h_fit hk
  have ef : s.ea (at_ .esi 0) = coeffAddr (fA' s₀) k := by
    rw [State.ea, at_, h.esi]; exact ea_ptr hp.f_fit hk
  have eg : s.ea (at_ .edi 0) = coeffAddr (gA' s₀) k := by
    rw [State.ea, at_, h.edi]; exact ea_ptr hp.g_fit hk
  refine hc _ s _ _ _ _ (hp.f_red k hk') (hp.g_red k hk') (fun e => (hp.h_red e) k hk')
    (by rw [ef]; exact hp.in_f h.rd hk) (by rw [ef, ← coeffAt_eq, hp.f_keep h.frame hk])
    (by rw [eg]; exact hp.in_g h.rd hk) (by rw [eg, ← coeffAt_eq, hp.g_keep h.frame hk])
    (by rw [eh]; exact hp.in_h' h.wr hk) (by rw [eh, ← coeffAt_eq, h.h k hk, ite_eq_right (Nat.lt_irrefl k)])
    fun s₂ o₂ v₂ => ?_
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [o₂.gpr r (by simp [h₁, h₂, h₃])]
  have m₂ : s₂.mem = s.mem := o₂.mem
  have r₂ : s₂.rd = (P0 s₀).rd := o₂.rd.trans h.rd
  have w₂ : s₂.wr = (P0 s₀).wr := o₂.wr.trans h.wr
  have ebp₂ : s₂.gpr .ebp = hP s₀ + BitVec.ofNat 32 (4 * k) := by
    rw [g₂ _ (by decide) (by decide) (by decide), h.ebp]
  have esi₂ : s₂.gpr .esi = fP' s₀ + BitVec.ofNat 32 (4 * k) := by
    rw [g₂ _ (by decide) (by decide) (by decide), h.esi]
  have edi₂ : s₂.gpr .edi = gP' s₀ + BitVec.ofNat 32 (4 * k) := by
    rw [g₂ _ (by decide) (by decide) (by decide), h.edi]
  have ecx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (256 - k) := by
    rw [g₂ _ (by decide) (by decide) (by decide), h.ecx]
  have out : InRegions s₂.wr (coeffAddr (hA s₀) k) 4 := hp.in_h w₂ hk
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mulTail, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store32, State.setReg, arithFlags, State.setFlags, ebp₂,
    ea_ptr hp.h_fit hk, out, ite_true, ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hv : s₂.gpr .ebx = newM V s₀ k := eq_ofNat_of_toNat v₂
  refine ⟨⟨by simp [g₂, h.esp], r₂, w₂, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · simp only [ite_true, ite_false, show Reg.ebp ≠ Reg.ecx by decide]
    exact ptr_next _ _ 4
  · simp only [ite_true, ite_false, show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide,
      show Reg.esi ≠ Reg.ebp by decide, esi₂]
    exact ptr_next _ _ 4
  · simp only [ite_true, ite_false, show Reg.edi ≠ Reg.ecx by decide, show Reg.edi ≠ Reg.ebp by decide, edi₂]
    exact ptr_next _ _ 4
  · simp only [ite_true, ecx₂]
    exact cnt_next hk
  · rw [m₂]; exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk')
  · dsimp only
    rw [coeffAt_writeW _ _ (show i < n from hi) hk', m₂, hv, h.h i hi]
    by_cases e : k = i
    · subst e; simp
    · rw [ite_eq_right e]
      by_cases hik : i < k
      · rw [ite_eq_left hik, ite_eq_left (by omega)]
      · rw [ite_eq_right hik, ite_eq_right (by omega)]
  · simp only [eval, ecx₂]
    exact cnt_ne hk (by decide)

/-! ## The functions -/

/-- The public data: the stack pointer and the pointers. -/
def MulPub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2

/-- The arguments, which the push leaves in place. -/
theorem MulPre.arg_P0 {acc : Bool} {s₀ : State} (hp : MulPre acc s₀) {i : Nat} (hi : i < 3) :
    ((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i ∧
      InRegions ((P0 s₀).rd ++ (P0 s₀).wr) (argAddr s₀ i) 4 ∧
      (P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have hc : (aR3 s₀).Contains (argAddr s₀ i) 4 := by
    have := hp.sp'
    simp only [argAddr, Region.Contains, E0] at this ⊢
    bv_omega
  refine ⟨?_, ⟨aR3 s₀, by simp [hp.wr], hc⟩, ?_⟩
  · rw [P0_esp]; simp only [argAddr, E0]; congr 1; bv_omega
  · exact (P0_mem hp.sp).readW hc (by simpa [← stk_eq hp.sp] using hp.stk_a.symm) (by decide)

theorem mulInit_piece (acc : Bool) (V : Nat → Nat → Nat → Nat) :
    Piece (MulPre acc) MulPub (fun s₀ s => s = P0 s₀) (MulInv V · 0) (.block mulInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    obtain ⟨a₀, i₀, v₀⟩ := hp.arg_P0 (i := 0) (by omega)
    obtain ⟨a₁, i₁, v₁⟩ := hp.arg_P0 (i := 1) (by omega)
    obtain ⟨a₂, i₂, v₂⟩ := hp.arg_P0 (i := 2) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at a₀ a₁ a₂
    apply WP.of_runBlock
    simp (config := {decide := true}) only [mulInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, a₁, a₂, i₀, i₁, i₂, v₀, v₁,
      v₂, ite_true, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, by simp, by simp, by simp, by simp, Frame.refl _ _, fun i hi => ?_⟩
    simp only [Nat.not_lt_zero, ite_false]
    exact hp.h_P0 hi
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

theorem mul_piece {core : List Instr} {acc : Bool} {V : Nat → Nat → Nat → Nat} (hc : CoreSpec core acc V)
    (hsp : NoSp (.seq (.block mulInit) (.loop (.block (core ++ mulTail)) .ne))) {hh : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .ebp, .esi, .edi, .ecx]) (.block (core ++ mulTail)) hh).isSome = true) :
    Piece (MulPre acc) MulPub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (MulInv V s₀ 256) s₀ s')
      (leaf (.seq (.block mulInit) (.loop (.block (core ++ mulTail)) .ne))) :=
  Piece.leaf (fun s₀ => [polyRegion (hA s₀)]) hsp (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← stk_eq hp.sp]; exact hp.stk_h, hp.ret_h⟩)
    (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (mulInit_piece acc V) (Piece.loop (fun k s₀ s => MulInv V s₀ k s) (by decide) fun k hk =>
      Piece.taint [.esp, .ebp, .esi, .edi, .ecx] (fun _ _ hp h => mul_step hc hp hk h)
        (fun s₀ s₀' s s' _ _ hq h h' r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
          · rw [h.ebp, h'.ebp, hP, hP, hq.2.1]
          · rw [h.esi, h'.esi, fP', fP', hq.2.2.1]
          · rw [h.edi, h'.edi, gP', gP', hq.2.2.2]
          · rw [h.ecx, h'.ecx]) ht)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- Memory with the arguments `0`, `0x400` and `0x800` at `0x5004`. -/
def mulSatMem : Mem := fun a => if a = 0x5009 then 4 else if a = 0x500d then 8 else 0

theorem mulSat_zero (a : Addr) (ha : a.toNat < 0x5000) : mulSatMem a = 0 := by
  simp only [mulSatMem]
  rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)]

theorem mul_verified : Verified X86.target mul (mulContract X86.abi 16) := by
  refine Piece.verified (((mul_piece mul_core (NoSp.of_all (by decide +kernel)) (by taint_decide)).pre_mono
    (fun _ h => MulPre.of_mul h) fun s s' _ _ h => by
      sig_pub [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    have hp := MulPre.of_mul h₀
    refine polyIs_of_toNat fun i hi => ?_
    rw [hinv.h i hi, ite_eq_left hi, mul_get _ _ hi, val_mul, polyAt_val hp.f_red hi, polyAt_val hp.g_red hi,
      newM, mulV, toNat_ofNat32 (mod_q_lt32 _)]
  · let st := satState mulSatMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 12⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 0x400 := by decide
    have a2 : arg st 2 = 0x800 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, reduced_below (mulSat_zero) 0x400 (by decide),
      reduced_below mulSat_zero 0x800 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)

theorem mulAdd_verified : Verified X86.target mulAdd (mulAddContract X86.abi 16) := by
  refine Piece.verified ((((mul_piece mulAdd_core (NoSp.of_all (by decide +kernel)) (by taint_decide)).pre_mono
    (fun _ h => MulPre.of_mulAdd h) fun s s' _ _ h => by
      sig_pub [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h)).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    have hp := MulPre.of_mulAdd h₀
    have hr := hp.h_red rfl
    refine polyIs_of_toNat fun i hi => ?_
    rw [hinv.h i hi, ite_eq_left hi, add_get _ _ hi, val_add', mul_get _ _ hi, val_mul, polyAt_val hp.f_red hi,
      polyAt_val hp.g_red hi, polyAt_val hr hi, newM, mulAddV, Nat.add_comm (_ % q),
      toNat_ofNat32 (mod_q_lt32 _)]
  · let st := satState mulSatMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 12⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 0x400 := by decide
    have a2 : arg st 2 = 0x800 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, reduced_below mulSat_zero 0 (by decide),
      reduced_below mulSat_zero 0x400 (by decide), reduced_below mulSat_zero 0x800 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)

end VG.Proof.MlDsa.X86.Arith
