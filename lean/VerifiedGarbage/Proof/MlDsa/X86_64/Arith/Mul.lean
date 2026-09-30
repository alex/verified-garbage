import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# ML-DSA on x86-64: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

Untrusted: everything here is checked by Lean. Both functions are one loop
over the coefficients (`Mul.fn_ok`), whose body stores the reduced product
(`mulBody_ok`), or the reduced sum of the product and the coefficient of
`h` (`mulAddBody_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly gprPreserved_of wp_counted ifp ifn ptr_step
  toNat_setWidth64)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-! ## One coefficient -/

/-- The product of two words, as `mul` leaves it. -/
abbrev prod32 (a b : BitVec 32) : BitVec 64 :=
  BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * (BitVec.setWidth 64 b).toNat)

theorem mulHead_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .r8) 4) :
    WP isa (.block mulHead) s fun s' =>
      (s'.gpr .rax = prod32 (s.mem.readW (s.gpr .rsi) 32) (s.mem.readW (s.gpr .r8) 32) ∧ s'.mem = s.mem) ∧
        Keep [.rax, .rdx, .r9] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold mulHead
  xrund [h1, h2]

theorem mulAddHead_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .r8) 4) (h3 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4) :
    WP isa (.block mulAddHead) s fun s' =>
      (s'.gpr .rax = prod32 (s.mem.readW (s.gpr .rsi) 32) (s.mem.readW (s.gpr .r8) 32) +
        BitVec.setWidth 64 (s.mem.readW (s.gpr .rdi) 32) ∧ s'.mem = s.mem) ∧ Keep [.rax, .rdx, .r9] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold mulAddHead mulHead
  xrund [h1, h2, h3, List.cons_append, List.nil_append]

theorem mulTail_ok (s : State) (hw : InRegions s.wr (s.gpr .rdi) 4) :
    WP isa (.block (([.store32 (at_ .rdi 0) .r10] : List Instr) ++ step3)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (BitVec.setWidth 32 (s.gpr .r10)) ∧ s'.gpr .rdi = s.gpr .rdi + 4 ∧
        s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .r8 = s.gpr .r8 + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rdi, .rsi, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold step3
  xrund [hw, List.cons_append, List.nil_append]

/-- A body: a head that leaves `x` in `rax`, `reduce`, and the store. -/
theorem body_ok {head : List Instr} {x : BitVec 64} (s : State)
    (hh : WP isa (.block head) s fun s' => (s'.gpr .rax = x ∧ s'.mem = s.mem) ∧ Keep [.rax, .rdx, .r9] s s')
    (hw : InRegions s.wr (s.gpr .rdi) 4) :
    WP isa (.block (head ++ reduce ++ ([.store32 (at_ .rdi 0) .r10] : List Instr) ++ step3)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (BitVec.setWidth 32 (redD x)) ∧ s'.gpr .rdi = s.gpr .rdi + 4 ∧
        s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .r8 = s.gpr .r8 + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdx, .r9, .r10, .r11, .rdi, .rsi, .r8, .rcx] s s' := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono hh fun s1 ⟨⟨ha, hm1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s1) fun s2 ⟨⟨hr, hm2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (mulTail_ok s2 (by rw [k12.2.2, k12.gpr (by decide)]; exact hw))
    fun s3 ⟨⟨hm3, hdi, hsi, h8, hcx, hz⟩, k3⟩ => ⟨?_, (k12.trans k3).mono (by decide)⟩
  rw [hm3, hdi, hsi, h8, hcx, hz, hr, hm2, ha, hm1, k12.gpr (r := .rdi) (by decide), k12.gpr (r := .rsi) (by decide),
    k12.gpr (r := .r8) (by decide), k12.gpr (r := .rcx) (by decide)]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem prod32_val {a b : BitVec 32} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    (BitVec.setWidth 32 (redD (prod32 a b))).toNat = (x * y).val := by
  have e : (prod32 a b).toNat = x.val * y.val := by
    rw [prod32, BitVec.toNat_ofNat, toNat_setWidth64, toNat_setWidth64, ha, hb]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (mul_lt_q2 x.isLt y.isLt) (by decide))
  rw [redD32_toNat, e, val_mul]

theorem prod32_add_val {a b c : BitVec 32} {x y z : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val)
    (hc : c.toNat = z.val) :
    (BitVec.setWidth 32 (redD (prod32 a b + BitVec.setWidth 64 c))).toNat = (z + x * y).val := by
  have e : (prod32 a b + BitVec.setWidth 64 c).toNat = x.val * y.val + z.val := by
    have := mul_lt_q2 x.isLt y.isLt
    have := val_lt z
    rw [BitVec.toNat_add, prod32, BitVec.toNat_ofNat, toNat_setWidth64, toNat_setWidth64, toNat_setWidth64, ha,
      hb, hc]
    omega
  rw [redD32_toNat, e, val_add', val_mul, Nat.add_comm, Nat.add_mod_mod]

/-! ## The loop -/

namespace Mul

/-- After `i` coefficients, each one `v k`. -/
structure Inv (s₀ : State) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (4 * i)
  rsi : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 (4 * i)
  r8 : s.gpr .r8 = s₀.gpr .rdx + BitVec.ofNat 64 (4 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rdi) k = if k < i then v k else coeffAt s₀.mem (s₀.gpr .rdi) k

section
variable {t : Poly → Poly → Poly → Poly} {r : Mem → Addr → Prop} {s₀ : State} (hp : (mulK t r).pre s₀)
include hp

theorem inR {p : Addr} (hp' : p = s₀.gpr .rsi ∨ p = s₀.gpr .rdx ∨ p = s₀.gpr .rdi) {k : Nat} (hk : k < 256)
    {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : InRegions (s.rd ++ s.wr) (coeffAddr p k) 4 := by
  rw [hrd, hwr, hp.1, hp.2.1]
  rcases hp' with rfl | rfl | rfl
  · exact ⟨_, by simp, coeff_contains _ hk⟩
  · exact ⟨_, by simp, coeff_contains _ hk⟩
  · exact ⟨_, by simp, coeff_contains _ hk⟩

theorem inW {k : Nat} (hk : k < 256) {s : State} (hwr : s.wr = s₀.wr) :
    InRegions s.wr (coeffAddr (s₀.gpr .rdi) k) 4 := by
  rw [hwr, hp.2.1]; exact ⟨_, by simp, coeff_contains _ hk⟩

/-- `f` and `g` are not written. -/
theorem coeffF {m : Mem} (hf : Frame [pR (s₀.gpr .rdi)] s₀.mem m) {k : Nat} (hk : k < 256) :
    coeffAt m (s₀.gpr .rsi) k = coeffAt s₀.mem (s₀.gpr .rsi) k :=
  coeffAt_frame hf (by simpa using hp.2.2.1.symm) hk

theorem coeffG {m : Mem} (hf : Frame [pR (s₀.gpr .rdi)] s₀.mem m) {k : Nat} (hk : k < 256) :
    coeffAt m (s₀.gpr .rdx) k = coeffAt s₀.mem (s₀.gpr .rdx) k :=
  coeffAt_frame hf (by simpa using hp.2.2.2.1.symm) hk

omit hp in
theorem inv_step {v : Nat → BitVec 32} {i : Nat} (hi : i < 256) {s s' : State} (hI : Inv s₀ v i s)
    (hm : s'.mem = s.mem.writeW (s.gpr .rdi) (v i)) (hdi : s'.gpr .rdi = s.gpr .rdi + 4)
    (hsi : s'.gpr .rsi = s.gpr .rsi + 4) (h8 : s'.gpr .r8 = s.gpr .r8 + 4) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Inv s₀ v (i + 1) s' where
  rdi := by rw [hdi, hI.rdi]; exact ptr_step _ i 4
  rsi := by rw [hsi, hI.rsi]; exact ptr_step _ i 4
  r8 := by rw [h8, hI.r8]; exact ptr_step _ i 4
  rd := hrd.trans hI.rd
  wr := hwr.trans hI.wr
  frame := by
    rw [hm, hI.rdi]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hi)
  coeff k hk := by
    rw [hm, hI.rdi, ← coeffAddr, coeffAt_writeW _ _ hk hi, hI.coeff k hk]
    by_cases e : i = k
    · subst e; simp
    · have : (k < i + 1) = (k < i) := propext (by omega)
      simp only [e, this, ↓reduceIte]

/-- What a body reads at coefficient `i`, and where. -/
theorem reads {v : Nat → BitVec 32} {i : Nat} (hi : i < 256) {s : State} (hI : Inv s₀ v i s) :
    s.mem.readW (s.gpr .rsi) 32 = coeffAt s₀.mem (s₀.gpr .rsi) i ∧
      s.mem.readW (s.gpr .r8) 32 = coeffAt s₀.mem (s₀.gpr .rdx) i ∧
      s.mem.readW (s.gpr .rdi) 32 = coeffAt s₀.mem (s₀.gpr .rdi) i ∧
      InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4 ∧ InRegions (s.rd ++ s.wr) (s.gpr .r8) 4 ∧
      InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4 ∧ InRegions s.wr (s.gpr .rdi) 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hI.rsi, ← coeffAddr, ← coeffAt_eq, coeffF hp hI.frame hi]
  · rw [hI.r8, ← coeffAddr, ← coeffAt_eq, coeffG hp hI.frame hi]
  · rw [hI.rdi, ← coeffAddr, ← coeffAt_eq, hI.coeff i hi]; simp only [Nat.lt_irrefl, ↓reduceIte]
  · rw [hI.rsi]; exact inR hp (.inl rfl) hi hI.rd hI.wr
  · rw [hI.r8]; exact inR hp (.inr (.inl rfl)) hi hI.rd hI.wr
  · rw [hI.rdi]; exact inR hp (.inr (.inr rfl)) hi hI.rd hI.wr
  · rw [hI.rdi]; exact inW hp hi hI.wr

/-- The whole function, from its precondition, with a body that stores
`v i` to coefficient `i`. -/
theorem fn_ok {body : List Instr} {v : Nat → BitVec 32}
    (hbody : ∀ i < 256, ∀ s, Inv s₀ v i s → WP isa (.block body) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (v i) ∧ s'.gpr .rdi = s.gpr .rdi + 4 ∧
        s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .r8 = s.gpr .r8 + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .r9, .r10, .r11, .rdi, .rsi, .r8, .rcx] s s')
    (hv : ∀ i < 256, (v i).toNat =
      ((t (polyAt s₀.mem (s₀.gpr .rdi)) (polyAt s₀.mem (s₀.gpr .rsi)) (polyAt s₀.mem (s₀.gpr .rdx)))[i]!).val)
    (hc : writesOnly [.rax, .rdx, .r9, .r10, .r11, .rdi, .rsi, .r8, .rcx]
      (.seq (.block [.mov .r8 (.reg .rdx)]) (.seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block body) .ne))) =
        true)
    (hm : Code.allInstrs (fun i => !loadsMxcsr i)
      (.seq (.block [.mov .r8 (.reg .rdx)]) (.seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block body) .ne)) :
        Prog isa) = true) :
    ∃ tr s', Exec isa (.seq (.block [.mov .r8 (.reg .rdx)])
        (.seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block body) .ne))) s₀ tr s' ∧
      abiPreserved s₀ s' ∧ (mulK t r).post s₀ s' := by
  obtain ⟨tr, s', he, hI, hk⟩ := WP.keep [.rax, .rdx, .r9, .r10, .r11, .rdi, .rsi, .r8, .rcx]
    (WP.seq (WP.mono (WP.keep [.r8] (Q := fun s => s.mem = s₀.mem ∧ s.gpr .r8 = s₀.gpr .rdx) (by xrund)
      (by decide)) fun s1 ⟨⟨hm1, h81⟩, k1⟩ =>
      wp_counted (s₀ := s1) (N := 256) (v := 256) rfl (by decide) (Inv s₀ v)
        (fun s hm hk' => ⟨by rw [hk'.gpr (by decide), k1.gpr (by decide)]; simp,
          by rw [hk'.gpr (by decide), k1.gpr (by decide)]; simp,
          by rw [hk'.gpr (by decide), h81]; simp, hk'.2.1.trans k1.2.1, hk'.2.2.trans k1.2.2,
          by rw [hm, hm1]; exact Frame.refl _ _, fun k _ => by simp [hm, hm1]⟩)
        fun i hi s hI => WP.mono (hbody i hi s hI) fun s' ⟨⟨hm, hdi, hsi, h8, hcx, hz⟩, hk⟩ =>
          ⟨inv_step hi hI hm hdi hsi h8 hk.2.1 hk.2.2, hcx, hz⟩)) hc
  refine ⟨tr, s', he, abiPreserved_of_exec hm he (gprPreserved_of hk (by decide) hI.frame
    (by simpa using hp.2.2.2.2.1)), polyIs_of_toNat fun i hi => ?_⟩
  rw [hI.coeff i hi, ifp hi]
  exact hv i hi

end

end Mul

/-! ## The functions -/

/-- The contract of `vg_mldsa_multiply_ntt`. -/
abbrev mulK' : Contract isa := mulK (fun _ f g => Spec.MlDsa.multiplyNTT f g) fun _ _ => True

/-- The contract of `vg_mldsa_multiply_add_ntt`. -/
abbrev mulAddK : Contract isa := mulK (fun h f g => Spec.MlDsa.add h (Spec.MlDsa.multiplyNTT f g)) Reduced

theorem mul_correct (s : State) (hs : mulK'.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.mul s t s' ∧ abiPreserved s s' ∧ mulK'.post s s' :=
  Mul.fn_ok hs (v := fun i => BitVec.setWidth 32 (redD (prod32 (coeffAt s.mem (s.gpr .rsi) i)
      (coeffAt s.mem (s.gpr .rdx) i))))
    (fun i hi s' hI => by
      obtain ⟨e1, e2, _, h1, h2, _, hw⟩ := Mul.reads hs hi hI
      have := body_ok s' (mulHead_ok s' h1 h2) hw
      rwa [e1, e2] at this)
    (fun i hi => by
      rw [mul_get _ _ hi]
      exact prod32_val (polyAt_val hs.2.2.2.2.2.2.2.2.1 hi).symm (polyAt_val hs.2.2.2.2.2.2.2.2.2 hi).symm)
    (by decide) (by decide)

theorem mulAdd_correct (s : State) (hs : mulAddK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Arith.mulAdd s t s' ∧ abiPreserved s s' ∧ mulAddK.post s s' :=
  Mul.fn_ok hs (v := fun i => BitVec.setWidth 32 (redD (prod32 (coeffAt s.mem (s.gpr .rsi) i)
      (coeffAt s.mem (s.gpr .rdx) i) + BitVec.setWidth 64 (coeffAt s.mem (s.gpr .rdi) i))))
    (fun i hi s' hI => by
      obtain ⟨e1, e2, e3, h1, h2, h3, hw⟩ := Mul.reads hs hi hI
      have := body_ok s' (mulAddHead_ok s' h1 h2 h3) hw
      rwa [e1, e2, e3] at this)
    (fun i hi => by
      rw [add_get _ _ hi, mul_get _ _ hi]
      exact prod32_add_val (polyAt_val hs.2.2.2.2.2.2.2.2.1 hi).symm
        (polyAt_val hs.2.2.2.2.2.2.2.2.2 hi).symm (polyAt_val hs.2.2.2.2.2.2.2.1 hi).symm)
    (by decide) (by decide)

/-- The pointers and `rsp` are public. -/
def mulτ : X86_64.Taint.T := X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]

theorem mul_agree {t : Poly → Poly → Poly → Poly} {r : Mem → Addr → Prop} (s₁ s₂ : State) (_ : (mulK t r).pre s₁)
    (_ : (mulK t r).pre s₂) (hp : (mulK t r).pub s₁ s₂) : X86_64.Taint.Agree mulτ s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

theorem mul_ct : ConstantTime isa mulK'.pre mulK'.pub Impl.MlDsa.X86_64.Arith.mul :=
  VG.Taint.constantTime (A := taint) mulτ mul_agree (by taint_decide)

theorem mulAdd_ct : ConstantTime isa mulAddK.pre mulAddK.pub Impl.MlDsa.X86_64.Arith.mulAdd :=
  VG.Taint.constantTime (A := taint) mulτ mul_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def mulSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem mul_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.mul (Spec.MlDsa.mulContract X86_64.abi) :=
  Verified.of_correct mul_correct mul_ct (by
    mldsa_implies [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using mulSat)

theorem mulAdd_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Arith.mulAdd (Spec.MlDsa.mulAddContract X86_64.abi) :=
  Verified.of_correct mulAdd_correct mulAdd_ct (by
    mldsa_implies [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using mulSat)

end VG.Proof.MlDsa.X86_64.Arith
