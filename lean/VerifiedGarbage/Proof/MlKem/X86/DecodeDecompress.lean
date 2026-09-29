import VerifiedGarbage.Proof.MlKem.X86.Unpack
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.Tauto

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_decode_decompress`

Untrusted: everything here is checked by Lean. The branch on `d` depends
only on `d`; each branch is a loop over groups of bytes, whose fields
`unpackSteps` (`Unpack.lean`) decompresses into the coefficients of
`decodeDecompress1`, `decodeDecompress4_*` and `decodeDecompress10_*`
(`Encode.lean`).
-/

namespace VG.Proof.MlKem.X86.DecodeDecompress

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)
abbrev bP : BitVec 32 := arg s₀ 0
abbrev lenV : BitVec 32 := arg s₀ 1
abbrev dV : BitVec 32 := arg s₀ 2
abbrev fP : BitVec 32 := arg s₀ 3
abbrev bA : Addr := (bP s₀).setWidth 64
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev bR : Region := ⟨bA s₀, (lenV s₀).toNat⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
abbrev dN : Nat := (dV s₀).toNat
/-- The input bytes. -/
abbrev B : List Byte := bytesAt s₀.mem (bA s₀) (lenV s₀).toNat
/-- The value of coefficient `i`. -/
abbrev V (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((decodeDecompress (dN s₀) (B s₀))[i]!).val
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [polyRegion (fA s₀), aR s₀]
  b_f : (bR s₀).Disjoint (polyRegion (fA s₀))
  b_a : (bR s₀).Disjoint (aR s₀)
  f_a : (polyRegion (fA s₀)).Disjoint (aR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (fA s₀))
  ret_a : (retR s₀).Disjoint (aR s₀)
  stk_b : (stkR s₀).Disjoint (bR s₀)
  stk_f : (stkR s₀).Disjoint (polyRegion (fA s₀))
  stk_a : (stkR s₀).Disjoint (aR s₀)
  b_fit : (bP s₀).toNat + (lenV s₀).toNat ≤ 2 ^ 32
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32
  d_mem : dN s₀ ∈ compressWidths
  len_eq : (lenV s₀).toNat = 32 * dN s₀

theorem Pre.of {s₀ : State} (h : (decodeDecompressContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [decodeDecompressContract, decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧ arg s₀ 3 = arg s₀' 3

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stk_eq : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem b_keep {s : State} (hf : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem) {j : Nat}
    (hj : j < (lenV s₀).toNat) : s.mem (bA s₀ + BitVec.ofNat 64 j) = (B s₀).getD j 0 := by
  have hf₁ := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf₁
  have l : (bR s₀).len ≤ 2 ^ 64 := by show (lenV s₀).toNat ≤ 2 ^ 64; have := (lenV s₀).isLt; omega
  rw [bytesAt_getD _ _ hj, hf.bytes (R := bR s₀) (by simpa using hp.b_f) l hj,
    hf₁.bytes (R := bR s₀) (by simpa [← hp.stk_eq] using hp.stk_b.symm) l hj]

theorem B_len : (B s₀).length = 32 * dN s₀ := by rw [B, bytesAt_length, hp.len_eq]

end Pre

/-- After `t` groups of `b` bytes and `c` coefficients, counting down from `N`. -/
structure Inv (s₀ : State) (c b N t : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = bP s₀ + BitVec.ofNat 32 (b * t)
  edi : s.gpr .edi = fP s₀ + BitVec.ofNat 32 (4 * c * t)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (N - t)
  frame : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem
  coef : ∀ i < c * t, coeffAt s.mem (fA s₀) i = V s₀ i

/-- The end of every branch. -/
structure Fin (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem
  coef : ∀ i < 256, coeffAt s.mem (fA s₀) i = V s₀ i

theorem Inv.fin {s₀ s : State} {c b N : Nat} (hN : c * N = 256) (h : Inv s₀ c b N N s) : Fin s₀ s :=
  ⟨h.esp, h.rd, h.wr, h.frame, fun i hi => h.coef i (by rw [hN]; exact hi)⟩

/-- Byte `o` of group `t`, from `esi`. -/
theorem byte_at {s₀ s : State} (hp : Pre s₀) {c b N t : Nat} (h : Inv s₀ c b N t s) {o : Nat}
    (ho : b * t + o < (lenV s₀).toNat) :
    s.ea (at_ .esi o) = bA s₀ + BitVec.ofNat 64 (b * t + o) ∧
      InRegions (s.rd ++ s.wr) (s.ea (at_ .esi o)) 1 ∧
      s.mem (s.ea (at_ .esi o)) = (B s₀).getD (b * t + o) 0 := by
  have fb := hp.b_fit
  have e : s.ea (at_ .esi o) = bA s₀ + BitVec.ofNat 64 (b * t + o) := by
    show (s.gpr .esi + BitVec.ofNat 32 o).setWidth 64 = _
    rw [h.esi, ea_add (by omega)]
  refine ⟨e, ?_, ?_⟩
  · rw [e]; exact ⟨bR s₀, by rw [h.rd, h.wr, pushed_rd, P0_wr, hp.rd]; simp, contains_at (by omega) fb⟩
  · rw [e, hp.b_keep h.frame ho]

/-- The coefficient addresses of group `t`, from `edi`. -/
theorem coef_at {s₀ s : State} (hp : Pre s₀) {c b N t : Nat} (h : Inv s₀ c b N t s) {j : Nat}
    (hj : c * t + j < 256) :
    s.ea (at_ .edi (4 * j)) = coeffAddr (fA s₀) (c * t + j) ∧
      InRegions s.wr (coeffAddr (fA s₀) (c * t + j)) 4 := by
  have ff := hp.f_fit
  refine ⟨?_, ⟨polyRegion (fA s₀), by rw [h.wr, P0_wr, hp.wr]; simp, coeff_contains _ (by rw [n_eq]; exact hj)⟩⟩
  show (s.gpr .edi + BitVec.ofNat 32 (4 * j)).setWidth 64 = _
  rw [h.edi, ea_add (by rw [show 4 * c * t = 4 * (c * t) from Nat.mul_assoc 4 c t]; omega)]
  congr 2; rw [Nat.mul_add, Nat.mul_assoc]

/-! ## `d` = 1 and 4: the coefficients of a byte -/

theorem val14 {s₀ : State} (hp : Pre s₀) {d k : Nat} (hd : dN s₀ = d) (hdk : d * k = 8)
    (hd14 : d = 1 ∨ d = 4) {t j : Nat} (ht : t < 32 * d) (hj : j < k) :
    BitVec.ofNat 32 (dfield d ((B s₀).getD t 0).toNat j) = V s₀ (k * t + j) := by
  have hdm : d ∈ compressWidths := hd ▸ hp.d_mem
  have lb := byte_lt ((B s₀).getD t 0)
  rw [V, dfield, dv_eq hdm (Nat.mod_lt _ (Nat.two_pow_pos d)), hd]
  refine congrArg (fun x : Zq => BitVec.ofNat 32 x.val) ?_
  rcases hd14 with rfl | rfl
  · obtain rfl : k = 8 := by omega
    rw [decodeDecompress1 _ (by rw [n_eq]; omega), show (8 * t + j) / 8 = t by omega,
      show (8 * t + j) % 8 = j by omega, Nat.one_mul, Nat.pow_one]
  · obtain rfl : k = 2 := by omega
    have hB : (B s₀).length = 128 := by rw [hp.B_len, hd]
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [Nat.add_zero, decodeDecompress4_even _ hB (by omega), Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    · rw [decodeDecompress4_odd _ hB (by omega)]
      refine congrArg (decompress 4) ?_
      omega

theorem step14 {s₀ : State} (hp : Pre s₀) {d k N : Nat} (hd : dN s₀ = d) (hdk : d * k = 8)
    (hd14 : d = 1 ∨ d = 4) (hN : N = 32 * d) {t : Nat} (ht : t < N) {s : State}
    (h : Inv s₀ k 1 N t s) :
    WP isa (.block (unpackBody d k)) s fun s' => Inv s₀ k 1 N (t + 1) s' ∧
      eval .ne s' = some (decide (t + 1 < N)) := by
  have hdm : d ∈ compressWidths := hd ▸ hp.d_mem
  have hl := hp.len_eq
  have hkt : k * t + k ≤ 256 := by
    rcases hd14 with rfl | rfl
    · obtain rfl : k = 8 := by omega
      omega
    · obtain rfl : k = 2 := by omega
      omega
  obtain ⟨eb, inb, vb⟩ := byte_at hp h (o := 0) (by rw [Nat.one_mul, Nat.add_zero]; omega)
  simp only [Nat.one_mul, Nat.add_zero] at eb vb
  refine wp_movzx inb ?_
  have ho₁ := Only.setReg s .ebx ((s.mem (s.ea (at_ .esi 0))).setWidth 32)
  refine unpackSteps_spec hdm (p := fA s₀) (i₀ := k * t) (B := ((B s₀).getD t 0).toNat) k _ _ _
    (by omega) (by omega) (by simp only [State.setReg, ite_true]; rw [vb, toNat_byte32])
    (fun j hj => by
      rw [← (coef_at hp h (j := j) (by omega)).1]
      simp only [State.ea, at_, State.setReg, show Reg.edi ≠ Reg.ebx by decide, ite_false])
    (fun j hj => by rw [ho₁.wr]; exact (coef_at hp h (j := j) (by omega)).2) fun s₂ o₂ f₂ c₂ => ?_
  have o := (Regs.of_only ho₁).trans o₂
  have g : ∀ r, r ∉ [Reg.ebx, .eax, .edx] → s₂.gpr r = s.gpr r := fun r hr =>
    o.gpr r (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
  have esi₂ := g .esi (by decide)
  have edi₂ := g .edi (by decide)
  have ecx₂ := g .ecx (by decide)
  have esp₂ := g .esp (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some, esi₂, edi₂, ecx₂, h.esi, h.edi,
    h.ecx, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [esp₂, h.esp], o.rd.trans h.rd, o.wr.trans h.wr, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide, ite_false, ite_true]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]; congr 2
  · simp only [show Reg.edi ≠ Reg.ecx by decide, ite_false, ite_true]
    rw [add_ofNat_add]; congr 2
  · simp only [ite_true]
    exact cnt_next ht
  · exact h.frame.trans f₂
  · intro i hi
    rw [Nat.mul_succ] at hi
    rw [c₂ i (by omega)]
    by_cases hr : k * t ≤ i ∧ i < k * t + k
    · rw [ite_eq_left hr, val14 hp hd hdk hd14 (by omega) (show i - k * t < k by omega),
        show k * t + (i - k * t) = i by omega]
    · rw [ite_eq_right hr]
      exact h.coef i (by omega)
  · simp only [eval]
    exact cnt_ne ht (by omega)

/-! ## `d` = 10: four coefficients of five bytes -/

theorem byteStep_spec (j : Nat) (is : List Instr) (s : State) (P : State → Prop) {A : Nat} {x : Byte}
    (hA : (s.gpr .ebx).toNat = A) (hAl : A < 2 ^ 24) (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi j)) 1)
    (hx : s.mem (s.ea (at_ .esi j)) = x)
    (k : ∀ s', Only [.eax, .ebx] s s' → (s'.gpr .ebx).toNat = A * 256 + x.toNat → WP isa (.block is) s' P) :
    WP isa (.block (byteStep j ++ is)) s P := by
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [byteStep, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    execShift, readSrc, State.load8, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    Option.map_some, hin, hx, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · simp only [ite_true]
    have := x.isLt
    rw [BitVec.toNat_add, rotr_small _ (by decide) (by decide) (by rw [hA]; exact hAl), hA, toNat_byte32,
      Nat.mod_eq_of_lt (by omega)]

theorem val10 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 10) {t : Nat} (ht : t < 64) {W : Nat}
    (hW : W = ((B s₀).getD (5 * t) 0).toNat + 256 * ((B s₀).getD (5 * t + 1) 0).toNat +
      65536 * ((B s₀).getD (5 * t + 2) 0).toNat + 16777216 * ((B s₀).getD (5 * t + 3) 0).toNat)
    {j : Nat} (hj : j < 3) :
    BitVec.ofNat 32 (dfield 10 W j) = V s₀ (4 * t + j) := by
  have hB : (B s₀).length = 320 := by rw [hp.B_len, hd]
  have hdm : (10 : Nat) ∈ compressWidths := by decide
  have l0 := byte_lt ((B s₀).getD (5 * t) 0)
  have l1 := byte_lt ((B s₀).getD (5 * t + 1) 0)
  have l2 := byte_lt ((B s₀).getD (5 * t + 2) 0)
  have l3 := byte_lt ((B s₀).getD (5 * t + 3) 0)
  rw [V, dfield, dv_eq hdm (Nat.mod_lt _ (Nat.two_pow_pos 10)), hd]
  refine congrArg (fun x : Zq => BitVec.ofNat 32 x.val) ?_
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
  · rw [Nat.add_zero, decodeDecompress10_0 _ hB ht]
    refine congrArg (decompress 10) ?_
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reducePow]
    omega
  · rw [decodeDecompress10_1 _ hB ht]
    refine congrArg (decompress 10) ?_
    simp only [Nat.mul_one, Nat.reducePow]
    omega
  · rw [decodeDecompress10_2 _ hB ht]
    refine congrArg (decompress 10) ?_
    simp only [Nat.reduceMul, Nat.reducePow]
    omega

theorem step10 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 10) {t : Nat} (ht : t < 64) {s : State}
    (h : Inv s₀ 4 5 64 t s) :
    WP isa (.block unpack10Body) s fun s' => Inv s₀ 4 5 64 (t + 1) s' ∧
      eval .ne s' = some (decide (t + 1 < 64)) := by
  have hdm : (10 : Nat) ∈ compressWidths := by decide
  have hl := hp.len_eq
  rw [hd] at hl
  have hB : (B s₀).length = 320 := by rw [hp.B_len, hd]
  obtain ⟨_, in0, v0⟩ := byte_at hp h (o := 0) (by omega)
  obtain ⟨_, in1, v1⟩ := byte_at hp h (o := 1) (by omega)
  obtain ⟨_, in2, v2⟩ := byte_at hp h (o := 2) (by omega)
  obtain ⟨_, in3, v3⟩ := byte_at hp h (o := 3) (by omega)
  obtain ⟨e4, in4, v4⟩ := byte_at hp h (o := 4) (by omega)
  simp only [Nat.add_zero] at v0
  have val : ∀ j < 3, BitVec.ofNat 32 (dfield 10 (((B s₀).getD (5 * t) 0).toNat +
      256 * ((B s₀).getD (5 * t + 1) 0).toNat + 65536 * ((B s₀).getD (5 * t + 2) 0).toNat +
      16777216 * ((B s₀).getD (5 * t + 3) 0).toNat) j) = V s₀ (4 * t + j) :=
    fun j hj => val10 hp hd ht rfl hj
  have v3' := decodeDecompress10_3 _ hB ht
  generalize (B s₀).getD (5 * t) 0 = b0 at v0 val
  generalize (B s₀).getD (5 * t + 1) 0 = b1 at v1 val
  generalize (B s₀).getD (5 * t + 2) 0 = b2 at v2 val
  generalize (B s₀).getD (5 * t + 3) 0 = b3 at v3 val v3'
  generalize eb4 : (B s₀).getD (5 * t + 4) 0 = b4 at v4 v3'
  have l0 := b0.isLt
  have l1 := b1.isLt
  have l2 := b2.isLt
  have l3 := b3.isLt
  have l4 := b4.isLt
  -- Registers that `Only` keeps keep the byte addresses.
  have tr : ∀ {ds : List Reg} {s' : State}, Only ds s s' → Reg.esi ∉ ds → ∀ o,
      s'.ea (at_ .esi o) = s.ea (at_ .esi o) ∧ s'.rd ++ s'.wr = s.rd ++ s.wr ∧ s'.mem = s.mem :=
    fun ho he o => ⟨by simp only [State.ea, at_, ho.gpr _ he], by rw [ho.rd, ho.wr], ho.mem⟩
  refine wp_movzx in3 ?_
  have o₁ := Only.setReg s .ebx ((s.mem (s.ea (at_ .esi 3))).setWidth 32)
  have t₁ := tr o₁ (by decide)
  refine byteStep_spec 2 _ _ _ (A := b3.toNat) (x := b2) (by simp only [State.setReg, ite_true, v3]; exact toNat_byte32 b3)
    (by omega) (by rw [(t₁ 2).1, (t₁ 2).2.1]; exact in2) (by rw [(t₁ 2).1, (t₁ 2).2.2]; exact v2)
    fun s₂ o₂ w₂ => ?_
  have t₂ := tr (o₁.trans o₂) (by decide)
  refine byteStep_spec 1 _ _ _ (x := b1) w₂ (by omega) (by rw [(t₂ 1).1, (t₂ 1).2.1]; exact in1)
    (by rw [(t₂ 1).1, (t₂ 1).2.2]; exact v1) fun s₃ o₃ w₃ => ?_
  have t₃ := tr ((o₁.trans o₂).trans o₃) (by decide)
  refine byteStep_spec 0 _ _ _ (x := b0) w₃ (by omega) (by rw [(t₃ 0).1, (t₃ 0).2.1]; exact in0)
    (by rw [(t₃ 0).1, (t₃ 0).2.2]; exact v0) fun s₄ o₄ w₄ => ?_
  have o₄' := ((o₁.trans o₂).trans o₃).trans o₄
  have g₄ : ∀ r, r ∉ [Reg.eax, .ebx] → s₄.gpr r = s.gpr r := fun r hr =>
    o₄'.gpr r (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
  refine unpackSteps_spec hdm (p := fA s₀) (i₀ := 4 * t) (B := b0.toNat + 256 * b1.toNat +
      65536 * b2.toNat + 16777216 * b3.toNat) 3 _ s₄ _ (by decide) (by omega) (by rw [w₄]; omega)
    (fun j hj => by
      rw [← (coef_at hp h (j := j) (by omega)).1]
      simp only [State.ea, at_, g₄ .edi (by decide)])
    (fun j hj => by rw [o₄'.wr]; exact (coef_at hp h (j := j) (by omega)).2) fun s₅ o₅ f₅ c₅ => ?_
  have o₅' := (Regs.of_only o₄').trans o₅
  have g₅ : ∀ r, r ∉ [Reg.eax, .ebx, .edx] → s₅.gpr r = s.gpr r := fun r hr =>
    o₅'.gpr r (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
  have esi₅ := g₅ .esi (by decide)
  have edi₅ := g₅ .edi (by decide)
  have ecx₅ := g₅ .ecx (by decide)
  have esp₅ := g₅ .esp (by decide)
  have bx₅ : s₅.gpr .ebx = s₄.gpr .ebx := o₅.gpr .ebx (by decide)
  have fr₅ : Frame [polyRegion (fA s₀)] (P0 s₀).mem s₅.mem := h.frame.trans (o₄'.mem ▸ f₅)
  have in4' : InRegions (s₅.rd ++ s₅.wr) ((s.gpr .esi + BitVec.ofNat 32 4).setWidth 64) 1 := by
    rw [o₅'.rd, o₅'.wr]; exact in4
  have v4' : s₅.mem ((s.gpr .esi + BitVec.ofNat 32 4).setWidth 64) = b4 := by
    rw [show (s.gpr .esi + BitVec.ofNat 32 4).setWidth 64 = s.ea (at_ .esi 4) from rfl, e4,
      hp.b_keep fr₅ (by omega), eb4]
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    execShift, readSrc, State.ea, at_, State.load8, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, Option.map_some, esi₅, in4', v4', bx₅, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  have hw : (s₄.gpr .ebx).toNat = b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
    rw [w₄]; omega
  have hy : b3.toNat / 64 + 4 * b4.toNat < 2 ^ 10 := by omega
  refine decomp_spec hdm _ _ _ (y := b3.toNat / 64 + 4 * b4.toNat) hy ?_ fun s₆ o₆ v₆ => ?_
  · simp only [ite_true]
    have e4 : (BitVec.setWidth 32 b4 + BitVec.setWidth 32 b4 + (BitVec.setWidth 32 b4 +
        BitVec.setWidth 32 b4)).toNat = 4 * b4.toNat := by
      simp only [BitVec.toNat_add, toNat_byte32]; omega
    rw [BitVec.toNat_add, toNat_shr, hw, e4]
    omega
  have g₆ : ∀ r, r ≠ .eax → r ≠ .edx → s₆.gpr r = s₅.gpr r := fun r h1 h2 => by
    rw [o₆.gpr r (by simp [h1, h2])]; simp [h1, h2]
  have esi₆ : s₆.gpr .esi = s.gpr .esi := by rw [g₆ _ (by decide) (by decide), esi₅]
  have edi₆ : s₆.gpr .edi = s.gpr .edi := by rw [g₆ _ (by decide) (by decide), edi₅]
  have ecx₆ : s₆.gpr .ecx = s.gpr .ecx := by rw [g₆ _ (by decide) (by decide), ecx₅]
  have esp₆ : s₆.gpr .esp = s.gpr .esp := by rw [g₆ _ (by decide) (by decide), esp₅]
  have m₆ : s₆.mem = s₅.mem := o₆.mem
  have wr₆ : s₆.wr = s.wr := by rw [o₆.wr]; exact o₅'.wr
  have rd₆ : s₆.rd = s.rd := by rw [o₆.rd]; exact o₅'.rd
  obtain ⟨ed3, out3⟩ := coef_at hp h (j := 3) (by omega)
  have ed3' : (s.gpr .edi + BitVec.ofNat 32 12).setWidth 64 = coeffAddr (fA s₀) (4 * t + 3) := ed3
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    esi₆, edi₆, ecx₆, m₆, wr₆, ed3', out3, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  have c3 : s₆.gpr .eax = V s₀ (4 * t + 3) := by
    rw [eq_ofNat_of_toNat v₆, V, hd, v3', dv_eq hdm hy]
  refine ⟨⟨by simp [esp₆, h.esp], rd₆.trans h.rd, h.wr, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide, ite_false, ite_true, h.esi]
    rw [show (5 : BitVec 32) = BitVec.ofNat 32 5 from rfl, add_ofNat_add]; congr 2
  · simp only [show Reg.edi ≠ Reg.ecx by decide, ite_false, ite_true, h.edi]
    rw [show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx]
    exact cnt_next ht
  · exact fr₅.writeW (List.mem_singleton_self _) _ (coeff_contains _ (by rw [n_eq]; omega))
  · intro i hi
    rw [coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) (show 4 * t + 3 < n by rw [n_eq]; omega)]
    by_cases e3 : 4 * t + 3 = i
    · rw [ite_eq_left e3, ← e3, c3]
    rw [ite_eq_right e3, c₅ i (by omega)]
    by_cases hr : 4 * t ≤ i ∧ i < 4 * t + 3
    · rw [ite_eq_left hr, show i = 4 * t + (i - 4 * t) by omega, Nat.add_sub_cancel_left]
      exact val (i - 4 * t) (by omega)
    · rw [ite_eq_right hr, o₄'.mem]
      exact h.coef i (by omega)
  · simp only [eval, h.ecx]
    exact cnt_ne ht (by omega)



/-! ## The function -/

/-- After `ddInit`, or the compare with `v`. -/
structure Init (s₀ : State) (v : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = bP s₀
  edi : s.gpr .edi = fP s₀
  eax : s.gpr .eax = dV s₀
  ev : eval .e s = some (decide (dN s₀ = v))

theorem pub_esp {s₀ s₀' : State} (hq : Pub s₀ s₀') : (P0 s₀).gpr .esp = (P0 s₀').gpr .esp := by
  rw [P0_esp, P0_esp, hq.1]

theorem init_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) (Init · 1) (.block ddInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₀ := P0_argAddr s₀ 0
    have a₂ := P0_argAddr s₀ 2
    have a₃ := P0_argAddr s₀ 3
    have i₀ := P0_argIn (s₀ := s₀) (n := 4) (i := 0) (by omega) fit (by simp [hp.wr])
    have i₂ := P0_argIn (s₀ := s₀) (n := 4) (i := 2) (by omega) fit (by simp [hp.wr])
    have i₃ := P0_argIn (s₀ := s₀) (n := 4) (i := 3) (by omega) fit (by simp [hp.wr])
    have v₀ := P0_arg hp.sp (n := 4) (i := 0) (by omega) fit hp.stk_a
    have v₂ := P0_arg hp.sp (n := 4) (i := 2) (by omega) fit hp.stk_a
    have v₃ := P0_arg hp.sp (n := 4) (i := 3) (by omega) fit hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at a₀ a₂ a₃
    apply WP.of_runBlock
    simp (config := {decide := true}) only [ddInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a₀, a₂, a₃, i₀, i₂, i₃, v₀, v₂, v₃, ite_true, ite_false,
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, rfl, by simp, by simp, by simp, ?_⟩
    simp only [eval, sub_beq_zero]
    rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', pub_esp hq]

theorem cmp4_piece : Piece Pre Pub (fun s₀ s => Init s₀ 1 s ∧ decide (dN s₀ = 1) = false)
    (fun s₀ s => Init s₀ 4 s ∧ dN s₀ ≠ 1) (.block [.alu .cmp .eax (.imm 4)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, h1⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨h.esp, h.rd, h.wr, h.mem, h.esi, h.edi, h.eax, ?_⟩, of_decide_eq_false h1⟩
  simp only [eval, sub_beq_zero, h.eax]
  rfl

theorem ecx_piece (d c b N : Nat) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 N))]) hc).isSome = true) :
    Piece Pre Pub (fun s₀ s => (∃ v, Init s₀ v s) ∧ dN s₀ = d)
      (fun s₀ s => Inv s₀ c b N 0 s ∧ dN s₀ = d) (.block [.mov .ecx (.imm (BitVec.ofNat 32 N))]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨v, h⟩, hd⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    ht
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, by simp [h.esi], by simp [h.edi], by simp,
    (by rw [h.mem]; exact Frame.refl _ _), fun j hj => absurd hj (by omega)⟩, hd⟩

theorem branch_piece {d c b N : Nat} (body : List Instr) (hN : 0 < N) (hcN : c * N = 256)
    (hstep : ∀ t < N, ∀ s₀ s, Pre s₀ → dN s₀ = d → Inv s₀ c b N t s →
      WP isa (.block body) s fun s' => Inv s₀ c b N (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < N)))
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block body) hc).isSome = true)
    {hc' : Taint.Hint VG.X86.Taint.T}
    (ht' : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 N))]) hc').isSome = true) :
    Piece Pre Pub (fun s₀ s => (∃ v, Init s₀ v s) ∧ dN s₀ = d) Fin (countedLoop N body) :=
  (Piece.seq (ecx_piece d c b N ht') (Piece.countLoop hN (fun t s₀ s => Inv s₀ c b N t s ∧ dN s₀ = d)
    [.esp, .esi, .edi, .ecx]
    (fun t ht s₀ s hp ⟨h, hd⟩ => (hstep t ht s₀ s hp hd h).mono fun _ ⟨h', e⟩ => ⟨⟨h', hd⟩, e⟩)
    (fun t _ s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.esp, h'.esp, pub_esp hq]
      · rw [h.esi, h'.esi, bP, bP, hq.2.1]
      · rw [h.edi, h'.edi, fP, fP, hq.2.2.2.2]
      · rw [h.ecx, h'.ecx]) ht)).mono (fun _ _ _ h => h) fun _ _ _ ⟨h, _⟩ => h.fin hcN

theorem ite_ev {v : Nat} {P : State → State → Prop} :
    ∀ s₀ s, Pre s₀ → Init s₀ v s ∧ P s₀ s → eval .e s = some (decide (dN s₀ = v)) :=
  fun _ _ _ h => h.1.ev

theorem ite_pub (v : Nat) : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
    decide (dN s₀ = v) = decide (dN s₀' = v) := fun _ _ _ _ hq => by rw [dN, dN, dV, dV, hq.2.2.2.1]

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Fin
    (.seq (.block ddInit)
      (.ite .e (countedLoop 32 (unpackBody 1 8))
        (.seq (.block [.alu .cmp .eax (.imm 4)])
          (.ite .e (countedLoop 128 (unpackBody 4 2)) (countedLoop 64 unpack10Body))))) := by
  refine Piece.seq (init_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h, trivial⟩)
    (Piece.ite _ (ite_ev (P := fun _ _ => True)) (ite_pub 1) ?_ ?_)
  · exact (branch_piece (d := 1) (c := 8) (b := 1) (unpackBody 1 8) (by decide) rfl
      (fun t ht s₀ s hp hd h => step14 hp hd (by decide) (.inl rfl) rfl ht h) (by taint_decide)
      (by taint_decide)).mono
      (fun _ _ _ ⟨⟨h, _⟩, e⟩ => ⟨⟨1, h⟩, of_decide_eq_true e⟩) fun _ _ _ h => h
  refine Piece.seq (cmp4_piece.mono (fun _ _ _ ⟨⟨h, _⟩, e⟩ => ⟨h, e⟩) fun _ _ _ h => h)
    (Piece.ite _ ite_ev (ite_pub 4) ?_ ?_)
  · exact (branch_piece (d := 4) (c := 2) (b := 1) (unpackBody 4 2) (by decide) rfl
      (fun t ht s₀ s hp hd h => step14 hp hd (by decide) (.inr rfl) rfl ht h) (by taint_decide)
      (by taint_decide)).mono
      (fun _ _ _ ⟨⟨h, _⟩, e⟩ => ⟨⟨4, h⟩, of_decide_eq_true e⟩) fun _ _ _ h => h
  · exact (branch_piece (d := 10) (c := 4) (b := 5) unpack10Body (by decide) rfl
      (fun t ht s₀ s hp hd h => step10 hp hd ht h) (by taint_decide) (by taint_decide)).mono
      (fun s₀ _ hp ⟨⟨h, h1⟩, e⟩ => ⟨⟨4, h⟩, by
        have := hp.d_mem
        have h4 := of_decide_eq_false e
        rcases mem_compressWidths this with h' | h' | h' <;> [exact absurd h' h1; exact absurd h' h4; exact h']⟩)
      fun _ _ _ h => h

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlKem.X86.decodeDecompress :=
  Piece.leaf (fun s₀ => [polyRegion (fA s₀)]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← hp.stk_eq]; exact hp.stk_f, hp.ret_f⟩)
    (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- Memory with the arguments `0`, `32`, `1` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5008 then 32 else if a = 0x500c then 1 else if a = 0x5011 then 4 else 0

theorem verified :
    Verified X86.target Impl.MlKem.X86.decodeDecompress (decodeDecompressContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [decodeDecompressContract, decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [decodeDecompressContract, decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    rw [hm]
    exact polyIs_of_coeffAt fun i hi => hinv.coef i (by rw [n_eq] at hi; exact hi)
  · let st := satState satMem [⟨0, 32⟩] [⟨0x400, 1024⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [decodeDecompressContract, decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlKem.X86.DecodeDecompress
