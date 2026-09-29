import VerifiedGarbage.Impl.MlKem.X86_64.Mul
import VerifiedGarbage.Proof.MlKem.X86_64.Reduce
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.MlKem.X86_64.Table

/-!
# ML-KEM on x86-64: `vg_mlkem_multiply_ntts`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `vg_mlkem_multiply_ntts(h = rdi, f = rsi, g = rdx, scratch = rcx)`. -/
def mulK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi), pR (s.gpr .rdx)] ∧ s.wr = [pR (s.gpr .rdi), pR (s.gpr .rcx)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rcx)) ∧
    (pR (s.gpr .rdx)).Disjoint (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdx)) ∧ (retR s).Disjoint (pR (s.gpr .rcx)) ∧
    Reduced s.mem (s.gpr .rsi) ∧ Reduced s.mem (s.gpr .rdx)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (multiplyNTTs (polyAt s.mem (s.gpr .rsi)) (polyAt s.mem (s.gpr .rdx)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

theorem gammaTab_eq {i : Nat} : gammaTab i = (gamma i).val := by
  rw [gamma, val_pow]; rfl

theorem gammaTab_lt (i : Nat) : gammaTab i < 3329 := Nat.mod_lt _ (by decide)

/-- The product of two 32-bit values, as `mul` leaves it. -/
abbrev prod32 (a b : BitVec 32) : BitVec 64 :=
  BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * (BitVec.setWidth 64 b).toNat)

theorem prod32_toNat {a b : BitVec 32} (h : a.toNat * b.toNat < 2 ^ 64) :
    (prod32 a b).toNat = a.toNat * b.toNat := by
  rw [prod32, BitVec.toNat_ofNat, toNat_setWidth64, toNat_setWidth64, Nat.mod_eq_of_lt h]

theorem mulA_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 4) 4)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 4) 4) :
    WP isa (.block [.mov32 .rax (.mem (at_ .rsi 4)), .mov32 .rdx (.mem (at_ .r8 4)), .mul .rdx]) s fun s' =>
      (s'.gpr .rax = prod32 (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 4) 32)
        (s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 4) 32) ∧ s'.mem = s.mem) ∧ Keep [.rax, .rdx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h1, h2]

theorem mulB_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .r8) 4) (h3 : InRegions (s.rd ++ s.wr) (s.gpr .r9) 4) :
    WP isa (.block [.mov32 .rax (.mem (at_ .r9 0)), .mul .r10, .mov .r11 (.reg .rax), .mov32 .rax (.mem (at_ .rsi 0)),
      .mov32 .rdx (.mem (at_ .r8 0)), .mul .rdx, .alu .add .rax (.reg .r11)]) s fun s' =>
      (s'.gpr .rax = prod32 (s.mem.readW (s.gpr .rsi) 32) (s.mem.readW (s.gpr .r8) 32) +
        BitVec.ofNat 64 ((BitVec.setWidth 64 (s.mem.readW (s.gpr .r9) 32)).toNat * (s.gpr .r10).toNat) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .rdx, .r11] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h1, h2, h3]

theorem mulC_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 4) 4)
    (h3 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 4) 4)
    (h4 : InRegions (s.rd ++ s.wr) (s.gpr .r8) 4) :
    WP isa (.block [.mov32 .rax (.mem (at_ .rsi 0)), .mov32 .rdx (.mem (at_ .r8 4)), .mul .rdx, .mov .r11 (.reg .rax),
      .mov32 .rax (.mem (at_ .rsi 4)), .mov32 .rdx (.mem (at_ .r8 0)), .mul .rdx, .alu .add .rax (.reg .r11)]) s
      fun s' => (s'.gpr .rax = prod32 (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 4) 32) (s.mem.readW (s.gpr .r8) 32) +
        prod32 (s.mem.readW (s.gpr .rsi) 32) (s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 4) 32) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .rdx, .r11] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h1, h2, h3, h4]

theorem store10_ok (s : State) (d : Nat) (h : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 d) 4) :
    WP isa (.block [.store32 (at_ .rdi d) .r10]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 d) (BitVec.setWidth 32 (s.gpr .r10))) ∧ Keep [] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [h]


/-! ## The body -/

/-- The word stored for coefficient `2i`. -/
def evenW (a0 a1 b0 b1 γ : BitVec 32) : BitVec 32 :=
  BitVec.setWidth 32 (redV (prod32 a0 b0 +
    BitVec.ofNat 64 ((BitVec.setWidth 64 γ).toNat * (redV (prod32 a1 b1)).toNat)))

/-- The word stored for coefficient `2i + 1`. -/
def oddW (a0 a1 b0 b1 : BitVec 32) : BitVec 32 :=
  BitVec.setWidth 32 (redV (prod32 a1 b0 + prod32 a0 b1))

theorem evenW_toNat {a0 a1 b0 b1 γ : BitVec 32} (ha0 : a0.toNat < q) (ha1 : a1.toNat < q)
    (hb0 : b0.toNat < q) (hb1 : b1.toNat < q) (hγ : γ.toNat < q) :
    (evenW a0 a1 b0 b1 γ).toNat = (a0.toNat * b0.toNat + γ.toNat * (a1.toNat * b1.toNat % q)) % q := by
  have p1 := mul_lt_q2 ha1 hb1
  have p0 := mul_lt_q2 ha0 hb0
  have e1 : (prod32 a1 b1).toNat = a1.toNat * b1.toNat := prod32_toNat (by omega)
  have r1 : (redV (prod32 a1 b1)).toNat = a1.toNat * b1.toNat % q := by
    rw [redV_toNat (by rw [e1]; omega), e1]
  have hr : a1.toNat * b1.toNat % q < q := Nat.mod_lt _ (by decide)
  have p2 := mul_lt_q2 hγ hr
  have e2 : (prod32 a0 b0 + BitVec.ofNat 64 ((BitVec.setWidth 64 γ).toNat * (redV (prod32 a1 b1)).toNat)).toNat =
      a0.toNat * b0.toNat + γ.toNat * (a1.toNat * b1.toNat % q) := by
    rw [BitVec.toNat_add, prod32_toNat (by omega), BitVec.toNat_ofNat, toNat_setWidth64, r1]
    rw [q_eq] at *; omega
  rw [evenW, toNat_setWidth32_64 (by
    have := redV_lt (x := prod32 a0 b0 + BitVec.ofNat 64 ((BitVec.setWidth 64 γ).toNat *
      (redV (prod32 a1 b1)).toNat)) (by rw [e2]; rw [q_eq] at *; omega)
    rw [q_eq] at this; omega), redV_toNat (by rw [e2]; rw [q_eq] at *; omega), e2]

theorem oddW_toNat {a0 a1 b0 b1 : BitVec 32} (ha0 : a0.toNat < q) (ha1 : a1.toNat < q)
    (hb0 : b0.toNat < q) (hb1 : b1.toNat < q) :
    (oddW a0 a1 b0 b1).toNat = (a0.toNat * b1.toNat + a1.toNat * b0.toNat) % q := by
  have p1 := mul_lt_q2 ha1 hb0
  have p0 := mul_lt_q2 ha0 hb1
  have e : (prod32 a1 b0 + prod32 a0 b1).toNat = a0.toNat * b1.toNat + a1.toNat * b0.toNat := by
    rw [BitVec.toNat_add, prod32_toNat (by omega), prod32_toNat (by omega)]
    rw [q_eq] at *; omega
  rw [oddW, toNat_setWidth32_64 (by
    have := redV_lt (x := prod32 a1 b0 + prod32 a0 b1) (by rw [e]; rw [q_eq] at *; omega)
    rw [q_eq] at this; omega), redV_toNat (by rw [e]; rw [q_eq] at *; omega), e]

/-- `mulEven`: coefficient `2i` to `[rdi]`. -/
theorem mulEven_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 4) 4)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .r8) 4)
    (h3 : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 4) 4)
    (h4 : InRegions (s.rd ++ s.wr) (s.gpr .r9) 4) (hw : InRegions s.wr (s.gpr .rdi) 4) :
    WP isa (.block mulEven) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdi) (evenW (s.mem.readW (s.gpr .rsi) 32)
        (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 4) 32) (s.mem.readW (s.gpr .r8) 32)
        (s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 4) 32) (s.mem.readW (s.gpr .r9) 32)) ∧
      Keep [.rax, .rdx, .r10, .r11] s s' := by
  unfold mulEven
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mulA_ok s h1 h3) fun s1 ⟨⟨ha1, hm1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s1) fun s2 ⟨⟨hr2, hm2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have g : ∀ r, r ∉ [Reg.rax, .rdx, .rax, .rdx, .r10, .r11] → s2.gpr r = s.gpr r := fun r hr => k12.gpr hr
  have hrr : s2.rd ++ s2.wr = s.rd ++ s.wr := by rw [k12.2.1, k12.2.2]
  rw [WP.block_append_iff]
  refine WP.mono (mulB_ok s2 (by rw [hrr, g .rsi (by decide)]; exact h0)
    (by rw [hrr, g .r8 (by decide)]; exact h2) (by rw [hrr, g .r9 (by decide)]; exact h4))
    fun s3 ⟨⟨hb3, hm3⟩, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s3) fun s4 ⟨⟨hr4, hm4⟩, k4⟩ => ?_
  have k14 := (k12.trans k3).trans k4
  have hw4 : InRegions s4.wr (s4.gpr .rdi + BitVec.ofNat 64 0) 4 := by
    rw [add_ofNat_zero, k14.2.2, k14.gpr (by decide)]; exact hw
  refine WP.mono (store10_ok s4 0 hw4) fun s5 ⟨hm5, k5⟩ => ⟨?_, (k14.trans k5).mono (by decide)⟩
  rw [hm5, add_ofNat_zero, k14.gpr (by decide), hr4, hb3, hm4, hm3, hm2, hm1, hr2, ha1,
    k12.gpr (r := .rsi) (by decide), k12.gpr (r := .r8) (by decide), k12.gpr (r := .r9) (by decide)]
  rfl

/-- `mulOdd`: coefficient `2i + 1` to `[rdi + 4]`. -/
theorem mulOdd_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 4) 4)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .r8) 4)
    (h3 : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 4) 4)
    (hw : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 4) 4) :
    WP isa (.block mulOdd) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 4) (oddW (s.mem.readW (s.gpr .rsi) 32)
        (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 4) 32) (s.mem.readW (s.gpr .r8) 32)
        (s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 4) 32)) ∧
      Keep [.rax, .rdx, .r10, .r11] s s' := by
  unfold mulOdd
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mulC_ok s h0 h3 h1 h2) fun s1 ⟨⟨ha1, hm1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s1) fun s2 ⟨⟨hr2, hm2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (store10_ok s2 4 (by rw [k12.2.2, k12.gpr (by decide)]; exact hw))
    fun s3 ⟨hm3, k3⟩ => ⟨?_, (k12.trans k3).mono (by decide)⟩
  rw [hm3, k12.gpr (by decide), hr2, hm2, ha1, hm1]
  rfl

theorem mulStep_ok (s : State) :
    WP isa (.block mulStep) s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rdi = s.gpr .rdi + 8 ∧ s'.gpr .rsi = s.gpr .rsi + 8 ∧
        s'.gpr .r8 = s.gpr .r8 + 8 ∧ s'.gpr .r9 = s.gpr .r9 + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rdi, .rsi, .r8, .r9, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold mulStep
  xrun


/-! ## Values -/

theorem even_val {F G : Poly} {i : Nat} (hi : i < 128) {a0 a1 b0 b1 γ : BitVec 32}
    (e0 : a0.toNat = (F[2 * i]!).val) (e1 : a1.toNat = (F[2 * i + 1]!).val)
    (f0 : b0.toNat = (G[2 * i]!).val) (f1 : b1.toNat = (G[2 * i + 1]!).val)
    (eγ : γ.toNat = (gamma i).val) :
    (evenW a0 a1 b0 b1 γ).toNat = ((multiplyNTTs F G)[2 * i]!).val := by
  rw [evenW_toNat (by rw [e0]; exact val_lt _) (by rw [e1]; exact val_lt _) (by rw [f0]; exact val_lt _)
    (by rw [f1]; exact val_lt _) (by rw [eγ]; exact val_lt _), multiplyNTTs_even F G hi, val_add', val_mul,
    val_mul, val_mul, e0, e1, f0, f1, eγ, Nat.add_mod (F[2 * i]!.val * G[2 * i]!.val), Nat.mul_comm (gamma i).val]

theorem odd_val {F G : Poly} {i : Nat} (hi : i < 128) {a0 a1 b0 b1 : BitVec 32}
    (e0 : a0.toNat = (F[2 * i]!).val) (e1 : a1.toNat = (F[2 * i + 1]!).val)
    (f0 : b0.toNat = (G[2 * i]!).val) (f1 : b1.toNat = (G[2 * i + 1]!).val) :
    (oddW a0 a1 b0 b1).toNat = ((multiplyNTTs F G)[2 * i + 1]!).val := by
  rw [oddW_toNat (by rw [e0]; exact val_lt _) (by rw [e1]; exact val_lt _) (by rw [f0]; exact val_lt _)
    (by rw [f1]; exact val_lt _), multiplyNTTs_odd F G hi, val_add', val_mul, val_mul, e0, e1, f0, f1,
    Nat.add_mod]

theorem gammaTab_toNat (i : Nat) : (BitVec.ofNat 32 (gammaTab i)).toNat = gammaTab i := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := gammaTab_lt i; omega)]

/-! ## The loop -/

namespace Mul

section
variable (s₀ : State)
abbrev hP : Addr := s₀.gpr .rdi
abbrev fP : Addr := s₀.gpr .rsi
abbrev gP : Addr := s₀.gpr .rdx
abbrev sP : Addr := s₀.gpr .rcx
/-- The value of coefficient `k` of the product. -/
abbrev val (k : Nat) : Nat := ((multiplyNTTs (polyAt s₀.mem (fP s₀)) (polyAt s₀.mem (gP s₀)))[k]!).val
end

/-- After `i` pairs. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = hP s₀ + BitVec.ofNat 64 (8 * i)
  rsi : s.gpr .rsi = fP s₀ + BitVec.ofNat 64 (8 * i)
  r8 : s.gpr .r8 = gP s₀ + BitVec.ofNat 64 (8 * i)
  r9 : s.gpr .r9 = sP s₀ + BitVec.ofNat 64 (4 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [pR (hP s₀), pR (sP s₀)] s₀.mem s.mem
  tab : Tab gammaTab s.mem (sP s₀) 128
  done : ∀ k < 2 * i, (coeffAt s.mem (hP s₀) k).toNat = val s₀ k

theorem addr8 (p : Addr) (i : Nat) : p + BitVec.ofNat 64 (8 * i) = coeffAddr p (2 * i) := by
  congr 2; omega

theorem addr8' (p : Addr) (i : Nat) :
    p + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 4 = coeffAddr p (2 * i + 1) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega

section
variable {s₀ : State} (hp : mulK.pre s₀)
include hp

theorem regions : s₀.rd ++ s₀.wr = [pR (fP s₀), pR (gP s₀), pR (hP s₀), pR (sP s₀)] := by
  rw [hp.1, hp.2.1]; rfl

theorem inR {p : Addr} (hp' : p = fP s₀ ∨ p = gP s₀ ∨ p = hP s₀ ∨ p = sP s₀) {k : Nat} (hk : k < 256) :
    InRegions (s₀.rd ++ s₀.wr) (coeffAddr p k) 4 := by
  rw [regions hp]
  rcases hp' with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp, coeff_contains _ hk⟩
  · exact ⟨_, by simp, coeff_contains _ hk⟩
  · exact ⟨_, by simp, coeff_contains _ hk⟩
  · exact ⟨_, by simp, coeff_contains _ hk⟩

theorem inW {k : Nat} (hk : k < 256) : InRegions s₀.wr (coeffAddr (hP s₀) k) 4 := by
  rw [hp.2.1]; exact ⟨_, by simp, coeff_contains _ hk⟩

/-- `f` and `g` are not written. -/
theorem coeffF {m : Mem} (hf : Frame [pR (hP s₀), pR (sP s₀)] s₀.mem m) {k : Nat} (hk : k < 256) :
    coeffAt m (fP s₀) k = coeffAt s₀.mem (fP s₀) k :=
  coeffAt_congr (bytes_frame hf (by simpa using ⟨hp.2.2.1.symm, hp.2.2.2.2.2.1⟩) (by decide)) hk

theorem coeffG {m : Mem} (hf : Frame [pR (hP s₀), pR (sP s₀)] s₀.mem m) {k : Nat} (hk : k < 256) :
    coeffAt m (gP s₀) k = coeffAt s₀.mem (gP s₀) k :=
  coeffAt_congr (bytes_frame hf (by simpa using ⟨hp.2.2.2.1.symm, hp.2.2.2.2.2.2.1⟩) (by decide)) hk

omit hp in
theorem sepH {p : Addr} (hd : (pR p).Disjoint (pR (hP s₀))) {k j : Nat} (hk : k < 256) (hj : j < 256) :
    Mem.Sep (coeffAddr p k) 4 (coeffAddr (hP s₀) j) (32 / 8) :=
  hd.sep (coeff_contains _ hk) (coeff_contains _ hj)

theorem step {i : Nat} (hi : i < 128) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block mulBody) s fun s' => Inv s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hrr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hI.rd, hI.wr]
  have i0 : 2 * i < 256 := by omega
  have i1 : 2 * i + 1 < 256 := by omega
  unfold mulBody
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (mulEven_ok s (by rw [hrr, hI.rsi, addr8]; exact inR hp (by simp) i0)
    (by rw [hrr, hI.rsi, addr8']; exact inR hp (by simp) i1)
    (by rw [hrr, hI.r8, addr8]; exact inR hp (by simp) i0)
    (by rw [hrr, hI.r8, addr8']; exact inR hp (by simp) i1)
    (by rw [hrr, hI.r9, ← coeffAddr]; exact inR hp (by simp) (show i < 256 by omega))
    (by rw [hI.wr, hI.rdi, addr8]; exact inW hp i0)) fun s1 ⟨hm1, k1⟩ => ?_
  have g1 : ∀ r, r ∉ [Reg.rax, .rdx, .r10, .r11] → s1.gpr r = s.gpr r := fun r hr => k1.gpr hr
  rw [WP.block_append_iff]
  refine WP.mono (mulOdd_ok s1 (by rw [k1.2.1, k1.2.2, hrr, g1 .rsi (by decide), hI.rsi, addr8]; exact inR hp (by simp) i0)
    (by rw [k1.2.1, k1.2.2, hrr, g1 .rsi (by decide), hI.rsi, addr8']; exact inR hp (by simp) i1)
    (by rw [k1.2.1, k1.2.2, hrr, g1 .r8 (by decide), hI.r8, addr8]; exact inR hp (by simp) i0)
    (by rw [k1.2.1, k1.2.2, hrr, g1 .r8 (by decide), hI.r8, addr8']; exact inR hp (by simp) i1)
    (by rw [k1.2.2, hI.wr, g1 .rdi (by decide), hI.rdi, addr8']; exact inW hp i1)) fun s2 ⟨hm2, k2⟩ => ?_
  have g2 : ∀ r, r ∉ [Reg.rax, .rdx, .r10, .r11] → s2.gpr r = s.gpr r := fun r hr => by
    rw [k2.gpr hr, g1 r hr]
  refine WP.mono (mulStep_ok s2) fun s3 ⟨⟨hm3, hdi, hsi, h8, h9, hcx, hz⟩, k3⟩ => ?_
  rw [g2 .rcx (by decide)] at hcx hz
  refine ⟨?_, hcx, hz⟩
  -- The memory.
  rw [g1 .rdi (by decide), g1 .rsi (by decide), g1 .r8 (by decide), hI.rdi, hI.rsi, hI.r8] at hm2
  rw [hI.rdi, hI.rsi, hI.r8, hI.r9, ← coeffAddr] at hm1
  simp only [addr8'] at hm1 hm2
  simp only [addr8] at hm1 hm2
  simp only [← coeffAt_eq] at hm1 hm2
  have dF : (pR (fP s₀)).Disjoint (pR (hP s₀)) := hp.2.2.1.symm
  have dG : (pR (gP s₀)).Disjoint (pR (hP s₀)) := hp.2.2.2.1.symm
  rw [hm1, coeffAt_writeW_sep _ _ _ (sepH dF i0 i0), coeffAt_writeW_sep _ _ _ (sepH dF i1 i0),
    coeffAt_writeW_sep _ _ _ (sepH dG i0 i0), coeffAt_writeW_sep _ _ _ (sepH dG i1 i0)] at hm2
  have ha0 := coeffF hp hI.frame i0
  have ha1 := coeffF hp hI.frame i1
  have hb0 := coeffG hp hI.frame i0
  have hb1 := coeffG hp hI.frame i1
  rw [ha0, ha1, hb0, hb1] at hm1 hm2
  have hF := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hG := hp.2.2.2.2.2.2.2.2.2.2.2.2
  have hγ : (coeffAt s.mem (sP s₀) i).toNat = (gamma i).val := by
    rw [hI.tab i (by omega), gammaTab_toNat, gammaTab_eq]
  refine ⟨?_, ?_, ?_, ?_, k3.2.1.trans (k2.2.1.trans (k1.2.1.trans hI.rd)),
    k3.2.2.trans (k2.2.2.trans (k1.2.2.trans hI.wr)), ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [hdi, g2 .rdi (by decide), hI.rdi]; exact ptr_step _ i 8
  · rw [hsi, g2 .rsi (by decide), hI.rsi]; exact ptr_step _ i 8
  · rw [h8, g2 .r8 (by decide), hI.r8]; exact ptr_step _ i 8
  · rw [h9, g2 .r9 (by decide), hI.r9]; exact ptr_step _ i 4
  · rw [hm3, hm2]
    exact (hI.frame.writeW (List.mem_cons_self ..) _ (coeff_contains _ i0)).writeW
      (List.mem_cons_self ..) _ (coeff_contains _ i1)
  · rw [hm3, hm2]
    have dS : (pR (sP s₀)).Disjoint (pR (hP s₀)) := hp.2.2.2.2.1.symm
    rw [coeffAt_writeW_sep _ _ _ (sepH dS (by omega) i1), coeffAt_writeW_sep _ _ _ (sepH dS (by omega) i0)]
    exact hI.tab k hk
  · rw [hm3, hm2, coeffAt_writeW _ _ (show k < 256 by omega) i1, coeffAt_writeW _ _ (show k < 256 by omega) i0]
    by_cases e1 : 2 * i + 1 = k
    · subst e1; rw [ifp rfl]
      exact odd_val hi (polyAt_val hF i0).symm (polyAt_val hF i1).symm (polyAt_val hG i0).symm
        (polyAt_val hG i1).symm
    · rw [ifn e1]
      by_cases e0 : 2 * i = k
      · subst e0; rw [ifp rfl]
        exact even_val hi (polyAt_val hF i0).symm (polyAt_val hF i1).symm (polyAt_val hG i0).symm
          (polyAt_val hG i1).symm hγ
      · rw [ifn e0]; exact hI.done k (by omega)

theorem prologue_ok :
    WP isa (.block (([.mov .r8 (.reg .rdx), .mov .r9 (.reg .rcx)] : List Instr) ++ storeTab gammaTab 128)) s₀
      fun s => Tab gammaTab s.mem (sP s₀) 128 ∧ Frame [pR (hP s₀), pR (sP s₀)] s₀.mem s.mem ∧
        Keep [.r8, .r9, .rax] s₀ s ∧ s.gpr .r8 = gP s₀ ∧ s.gpr .r9 = sP s₀ := by
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r8, .r9]
    (Q := fun s => s.mem = s₀.mem ∧ s.gpr .r8 = gP s₀ ∧ s.gpr .r9 = sP s₀) (by xrun) (by decide))
    fun s1 ⟨⟨hm, h8, h9⟩, k1⟩ => ?_
  refine WP.mono (storeTab_ok gammaTab (by decide) s1 (by rw [k1.2.2, hp.2.1, h9]; simp))
    fun s ⟨ht, hf, hk⟩ => ⟨by rw [← h9]; exact ht, by rw [← hm]; exact (hf.mono (by simp [h9])),
      k1.trans hk, by rw [hk.gpr (by decide), h8], by rw [hk.gpr (by decide), h9]⟩

theorem correct : ∃ t s', Exec isa Impl.MlKem.X86_64.multiplyNTTs s₀ t s' ∧ abiPreserved s₀ s' ∧
    mulK.post s₀ s' := by
  obtain ⟨t, s', he, hI, hk⟩ := WP.keep (c := Impl.MlKem.X86_64.multiplyNTTs)
    [.rax, .rdx, .rdi, .rsi, .rcx, .r8, .r9, .r10, .r11]
    (WP.seq (WP.mono (prologue_ok hp) fun sp ⟨ht, hf, hk, h8, h9⟩ =>
      wp_counted (s₀ := sp) (N := 128) (v := 128) rfl (by decide) (Inv s₀)
        (fun s hm hk' => ⟨by rw [hk'.gpr (by decide), hk.gpr (by decide)]; simp,
          by rw [hk'.gpr (by decide), hk.gpr (by decide)]; simp,
          by rw [hk'.gpr (by decide), h8]; simp, by rw [hk'.gpr (by decide), h9]; simp,
          hk'.2.1.trans hk.2.1, hk'.2.2.trans hk.2.2, by rw [hm]; exact hf, by rw [hm]; exact ht,
          fun _ h => absurd h (Nat.not_lt_zero _)⟩)
        fun i hi s hI => step hp hi hI)) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hI.frame
    (by simpa using ⟨hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1⟩)),
    polyIs_of_toNat fun k hk => hI.done k (by omega)⟩

end

end Mul

theorem mul_correct (s : State) (hs : mulK.pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.multiplyNTTs s t s' ∧ abiPreserved s s' ∧ mulK.post s s' :=
  Mul.correct hs

theorem mul_ct : ConstantTime isa mulK.pre mulK.pub Impl.MlKem.X86_64.multiplyNTTs :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def mulSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x4000, 1024⟩]

theorem mul_verified :
    Verified X86_64.target Impl.MlKem.X86_64.multiplyNTTs (Spec.MlKem.mulContract X86_64.abi) :=
  Verified.of_correct mul_correct mul_ct (by
    mlkem_implies [Spec.MlKem.mulContract, Spec.MlKem.mulSig, mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using mulSat)

end VG.Proof.MlKem.X86_64
