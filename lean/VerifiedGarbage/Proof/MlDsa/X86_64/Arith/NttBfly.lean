import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.Arith.Ntt

/-!
# ML-DSA on x86-64: the butterflies of `NTT` and `NTT⁻¹`

Untrusted: everything here is checked by Lean. What one butterfly's code
stores (`bfly_ok`, `bflyInv_ok`), for any `len`, from the words it reads
and the zeta in `r9`; and that it does what the butterfly of the
specification does (`bfly_spec`, `bflyInv_spec`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-! ## `NTT` -/

/-- The part of `bfly` after the product is reduced. -/
def bflyTail (len : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi 0)), .mov32 .rdx (.reg .rax), .alu32 .add .rdx (.imm qImm),
      .alu32 .sub .rdx (.reg .r10)] ++ csubQ .rdx .r11 ++
    [.store32 (at_ .rsi (4 * len)) .rdx, .alu32 .add .rax (.reg .r10)] ++ csubQ .rax .r11 ++
    [.store32 (at_ .rsi 0) .rax, .alu .add .rsi (.imm 4), .alu .sub .rcx (.imm 1)]

theorem bfly_eq (len : Nat) :
    Impl.MlDsa.X86_64.Arith.bfly len =
      ([.mov32 .rax (.mem (at_ .rsi (4 * len))), .mul .r9] : List Instr) ++ (reduce ++ bflyTail len) := by
  simp only [Impl.MlDsa.X86_64.Arith.bfly, bflyTail, List.append_assoc]

theorem bflyHead_ok (len : Nat) (s : State)
    (h : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4) :
    WP isa (.block ([.mov32 .rax (.mem (at_ .rsi (4 * len))), .mul .r9] : List Instr)) s fun s' =>
      (s'.gpr .rax = prodW (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32) (s.gpr .r9) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .rdx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrund [h]

theorem bflyTail_ok (len : Nat) (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (w0 : InRegions s.wr (s.gpr .rsi) 4) (w1 : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4) :
    WP isa (.block (bflyTail len)) s fun s' =>
      (s'.mem = (s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * len))
          (csubD (s.mem.readW (s.gpr .rsi) 32 + qImm - BitVec.setWidth 32 (s.gpr .r10)))).writeW (s.gpr .rsi)
          (csubD (s.mem.readW (s.gpr .rsi) 32 + BitVec.setWidth 32 (s.gpr .r10))) ∧
        s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .rsi, .rcx, .r11] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold bflyTail csubQ
  xrund [h0, w0, w1, List.cons_append, List.nil_append, csubD]

theorem bfly_ok (len : Nat) (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4)
    (w0 : InRegions s.wr (s.gpr .rsi) 4) (w1 : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4) :
    WP isa (.block (Impl.MlDsa.X86_64.Arith.bfly len)) s fun s' =>
      (s'.mem = (s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * len))
          (csubD (s.mem.readW (s.gpr .rsi) 32 + qImm - BitVec.setWidth 32
            (redD (prodW (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32) (s.gpr .r9)))))).writeW
          (s.gpr .rsi) (csubD (s.mem.readW (s.gpr .rsi) 32 + BitVec.setWidth 32
            (redD (prodW (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32) (s.gpr .r9))))) ∧
        s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .rsi, .rcx, .r10, .r11] s s' := by
  rw [bfly_eq, WP.block_append_iff]
  refine WP.mono (bflyHead_ok len s h1) fun s1 ⟨⟨ha, hm1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s1) fun s2 ⟨⟨hr, hm2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hsi : s2.gpr .rsi = s.gpr .rsi := k12.gpr (by decide)
  have hrr : s2.rd ++ s2.wr = s.rd ++ s.wr := by rw [k12.2.1, k12.2.2]
  refine WP.mono (bflyTail_ok len s2 (by rw [hrr, hsi]; exact h0) (by rw [k12.2.2, hsi]; exact w0)
    (by rw [k12.2.2, hsi]; exact w1)) fun s3 ⟨⟨hm3, h3si, h3cx, h3z⟩, k3⟩ => ⟨?_, (k12.trans k3).mono (by decide)⟩
  have hcx : s2.gpr .rcx = s.gpr .rcx := k12.gpr (by decide)
  rw [hm3, h3si, h3cx, h3z, hcx, hsi, hr, hm2, hm1, ha]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## `NTT⁻¹` -/

/-- The part of `bflyInv` up to the product. -/
def bflyInvHead (len : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi 0)), .mov32 .r10 (.mem (at_ .rsi (4 * len))), .mov32 .rdx (.reg .rax),
    .alu32 .add .rdx (.reg .r10)] ++ csubQ .rdx .r11 ++
    [.store32 (at_ .rsi 0) .rdx, .alu32 .add .rax (.imm qImm), .alu32 .sub .rax (.reg .r10)] ++
    csubQ .rax .r11 ++ [.mul .r9]

theorem bflyInv_eq (len : Nat) :
    Impl.MlDsa.X86_64.Arith.bflyInv len = bflyInvHead len ++ (reduce ++ ([.store32 (at_ .rsi (4 * len)) .r10,
      .alu .add .rsi (.imm 4), .alu .sub .rcx (.imm 1)] : List Instr)) := by
  simp only [Impl.MlDsa.X86_64.Arith.bflyInv, bflyInvHead, List.append_assoc]

theorem bflyInvHead_ok (len : Nat) (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4)
    (w0 : InRegions s.wr (s.gpr .rsi) 4) :
    WP isa (.block (bflyInvHead len)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rsi) (csubD (s.mem.readW (s.gpr .rsi) 32 +
          s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32)) ∧
        s'.gpr .rax = prodW (csubD (s.mem.readW (s.gpr .rsi) 32 + qImm -
          s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32)) (s.gpr .r9)) ∧
      Keep [.rax, .rdx, .r10, .r11] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold bflyInvHead csubQ
  xrund [h0, h1, w0, List.cons_append, List.nil_append, csubD]

theorem bflyInv_ok (len : Nat) (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4)
    (w0 : InRegions s.wr (s.gpr .rsi) 4) (w1 : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4) :
    WP isa (.block (Impl.MlDsa.X86_64.Arith.bflyInv len)) s fun s' =>
      (s'.mem = (s.mem.writeW (s.gpr .rsi) (csubD (s.mem.readW (s.gpr .rsi) 32 +
          s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32))).writeW
          (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) (BitVec.setWidth 32 (redD (prodW
            (csubD (s.mem.readW (s.gpr .rsi) 32 + qImm - s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32))
            (s.gpr .r9)))) ∧
        s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .rsi, .rcx, .r10, .r11] s s' := by
  rw [bflyInv_eq, WP.block_append_iff]
  refine WP.mono (bflyInvHead_ok len s h0 h1 w0) fun s1 ⟨⟨hm1, ha⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s1) fun s2 ⟨⟨hr, hm2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hsi : s2.gpr .rsi = s.gpr .rsi := k12.gpr (by decide)
  have hcx : s2.gpr .rcx = s.gpr .rcx := k12.gpr (by decide)
  refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun s' => s'.mem = s2.mem.writeW (s2.gpr .rsi + BitVec.ofNat 64 (4 * len))
      (BitVec.setWidth 32 (s2.gpr .r10)) ∧ s'.gpr .rsi = s2.gpr .rsi + 4 ∧ s'.gpr .rcx = s2.gpr .rcx - 1 ∧
      s'.zf = some (s2.gpr .rcx - 1 == 0)) (by
        xrund [show InRegions s2.wr (s2.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4 by rw [k12.2.2, hsi]; exact w1])
      (by rfl)) fun s3 ⟨⟨hm3, h3si, h3cx, h3z⟩, k3⟩ => ⟨?_, (k12.trans k3).mono (by decide)⟩
  rw [hm3, h3si, h3cx, h3z, hcx, hsi, hr, hm2, hm1, ha]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## What they do to a stored polynomial -/

/-- The code `code len` of a butterfly does what `op` does. -/
def BflyOk (code : Nat → List Instr) (op : Poly → Nat → Nat → Zq → Poly) : Prop :=
  ∀ (fP : Addr) (len j : Nat), 0 < len → j + len < 256 → ∀ (z : Zq) (F : Poly) (s : State),
    s.gpr .rsi = coeffAddr fP j → s.gpr .r9 = BitVec.ofNat 64 z.val → PolyIs s.mem fP F → pR fP ∈ s.wr →
    WP isa (.block (code len)) s fun s' => (PolyIs s'.mem fP (op F j len z) ∧ Frame [pR fP] s.mem s'.mem ∧
      s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdx, .rsi, .rcx, .r10, .r11] s s'

/-- The words a butterfly reads. -/
theorem bfly_regions {fP : Addr} {len j : Nat} (hj : j + len < 256) {s : State}
    (hsi : s.gpr .rsi = coeffAddr fP j) (hw : pR fP ∈ s.wr) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4 ∧ InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4 ∧
      InRegions s.wr (s.gpr .rsi) 4 ∧ InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4 := by
  rw [hsi, coeffAddr_add]
  exact ⟨⟨_, List.mem_append_right _ hw, coeff_contains _ (show j < 256 by omega)⟩,
    ⟨_, List.mem_append_right _ hw, coeff_contains _ hj⟩, ⟨_, hw, coeff_contains _ (show j < 256 by omega)⟩,
    ⟨_, hw, coeff_contains _ hj⟩⟩

/-- The two writes of a butterfly are within the polynomial. -/
theorem bfly_frame {fP : Addr} {len j : Nat} (hj : j + len < 256) (m : Mem) (a b : BitVec 32) :
    Frame [pR fP] m ((m.writeW (coeffAddr fP (j + len)) a).writeW (coeffAddr fP j) b) ∧
      Frame [pR fP] m ((m.writeW (coeffAddr fP j) a).writeW (coeffAddr fP (j + len)) b) :=
  ⟨(Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ (coeff_contains _ hj)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (show j < 256 by omega)),
    (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show j < 256 by omega))).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hj)⟩

theorem bfly_spec : BflyOk Impl.MlDsa.X86_64.Arith.bfly Arith.bfly := by
  intro fP len j hlen hj z F s hsi h9 hF hw
  obtain ⟨r0, r1, w0, w1⟩ := bfly_regions hj hsi hw
  refine WP.mono (bfly_ok len s r0 r1 w0 w1) fun s' ⟨⟨hm, hsi', hcx, hz⟩, hk⟩ => ⟨⟨?_, ?_, hsi', hcx, hz⟩, hk⟩
  · rw [hm, h9, hsi, coeffAddr_add, ← coeffAt_eq, ← coeffAt_eq]
    have hj' : j < 256 := by omega
    have ha := polyIs_toNat hF hj'
    have hT := redD_prodW (z := z) (polyIs_toNat hF hj)
    show PolyIs _ _ ((F.set! (j + len) (F[j]! - z * F[j + len]!)).set! j
      ((F.set! (j + len) (F[j]! - z * F[j + len]!))[j]! + z * F[j + len]!))
    rw [getElem!_set!_ne _ hj' (by omega)]
    exact polyIs_writeW (polyIs_writeW hF hj _ (csubD_sub_val ha hT)) hj' _ (csubD_add_val ha hT)
  · rw [hm, hsi, coeffAddr_add]
    exact (bfly_frame hj _ _ _).1

theorem bflyInv_spec : BflyOk Impl.MlDsa.X86_64.Arith.bflyInv Arith.bflyInv := by
  intro fP len j hlen hj z F s hsi h9 hF hw
  obtain ⟨r0, r1, w0, w1⟩ := bfly_regions hj hsi hw
  refine WP.mono (bflyInv_ok len s r0 r1 w0 w1) fun s' ⟨⟨hm, hsi', hcx, hz⟩, hk⟩ => ⟨⟨?_, ?_, hsi', hcx, hz⟩, hk⟩
  · rw [hm, h9, hsi, coeffAddr_add, ← coeffAt_eq, ← coeffAt_eq]
    have hj' : j < 256 := by omega
    have ha := polyIs_toNat hF hj'
    have hu := polyIs_toNat hF hj
    have hne : j ≠ j + len := by omega
    show PolyIs _ _ (((F.set! j (F[j]! + F[j + len]!)).set! (j + len)
      (F[j]! - (F.set! j (F[j]! + F[j + len]!))[j + len]!)).set! (j + len)
      (z * ((F.set! j (F[j]! + F[j + len]!)).set! (j + len)
        (F[j]! - (F.set! j (F[j]! + F[j + len]!))[j + len]!))[j + len]!))
    rw [getElem!_set!_ne _ hj hne, getElem!_set!_self _ hj]
    have e : ∀ (G : Poly) (x y : Zq), (G.set! (j + len) x).set! (j + len) y = G.set! (j + len) y := fun G x y =>
      ext_getElem! fun i hi => by
        by_cases h : i = j + len
        · subst h; rw [getElem!_set!_self _ hi, getElem!_set!_self _ hi]
        · rw [getElem!_set!_ne _ hi (Ne.symm h), getElem!_set!_ne _ hi (Ne.symm h), getElem!_set!_ne _ hi (Ne.symm h)]
    rw [e]
    exact polyIs_writeW (polyIs_writeW hF hj' _ (csubD_add_val ha hu)) hj _
      (redD_prodW (csubD_sub_val ha hu))
  · rw [hm, hsi, coeffAddr_add]
    exact (bfly_frame hj _ _ _).2

end VG.Proof.MlDsa.X86_64.Arith
