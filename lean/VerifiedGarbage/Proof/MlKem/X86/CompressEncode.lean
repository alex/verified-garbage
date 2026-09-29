import VerifiedGarbage.Proof.MlKem.X86.Pack
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.Tauto

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_compress_encode`

Untrusted: everything here is checked by Lean. The branch on `d` depends
only on `d`; each branch is a loop over groups of coefficients, packed with
`accSteps` (`Pack.lean`) into the bytes of `compressEncode1`,
`compressEncode4` and `compressEncode10_*` (`Encode.lean`).
-/

namespace VG.Proof.MlKem.X86.CompressEncode

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)
abbrev fP : BitVec 32 := arg s₀ 0
abbrev dV : BitVec 32 := arg s₀ 1
abbrev oP : BitVec 32 := arg s₀ 2
abbrev lenV : BitVec 32 := arg s₀ 3
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev oA : Addr := (oP s₀).setWidth 64
abbrev oR : Region := ⟨oA s₀, (lenV s₀).toNat⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
abbrev dN : Nat := (dV s₀).toNat
/-- The encoding. -/
abbrev L : List Byte := compressEncode (dN s₀) (polyAt s₀.mem (fA s₀))
/-- Compressed coefficient `i`. -/
abbrev C (i : Nat) : Nat := compress (dN s₀) (polyAt s₀.mem (fA s₀))[i]!
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (fA s₀)]
  wr : s₀.wr = [oR s₀, aR s₀]
  f_o : (polyRegion (fA s₀)).Disjoint (oR s₀)
  f_a : (polyRegion (fA s₀)).Disjoint (aR s₀)
  o_a : (oR s₀).Disjoint (aR s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (fA s₀))
  ret_o : (retR s₀).Disjoint (oR s₀)
  ret_a : (retR s₀).Disjoint (aR s₀)
  stk_f : (stkR s₀).Disjoint (polyRegion (fA s₀))
  stk_o : (stkR s₀).Disjoint (oR s₀)
  stk_a : (stkR s₀).Disjoint (aR s₀)
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32
  o_fit : (oP s₀).toNat + (lenV s₀).toNat ≤ 2 ^ 32
  d_mem : dN s₀ ∈ compressWidths
  len_eq : (lenV s₀).toNat = 32 * dN s₀
  f_red : Reduced s₀.mem (fA s₀)

theorem Pre.of {s₀ : State} (h : (compressEncodeContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [compressEncodeContract, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧ arg s₀ 3 = arg s₀' 3

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stk_eq : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem f_keep {s : State} (hf : Frame [oR s₀] (P0 s₀).mem s.mem) {i : Nat} (hi : i < 256) :
    coeffAt s.mem (fA s₀) i = coeffAt s₀.mem (fA s₀) i := by
  have hf₁ := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf₁
  refine coeffAt_congr (fun j hj => ?_) hi
  rw [hf.bytes (R := polyRegion (fA s₀)) (by simpa using hp.f_o) (polyLen _) hj,
    hf₁.bytes (R := polyRegion (fA s₀)) (by simpa [← hp.stk_eq] using hp.stk_f.symm) (polyLen _) hj]

/-- `C i` from what the coefficient holds in memory. -/
theorem C_eq {i : Nat} (hi : i < 256) :
    C s₀ i = cf (dN s₀) (coeffAt s₀.mem (fA s₀) i).toNat := by
  rw [cf_eq hp.d_mem (hp.f_red i hi), C, polyAt_get _ _ hi]

end Pre

/-- After `t` groups of `c` coefficients and `b` bytes, counting down from `N`. -/
structure Inv (s₀ : State) (c b N t : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = fP s₀ + BitVec.ofNat 32 (4 * c * t)
  edi : s.gpr .edi = oP s₀ + BitVec.ofNat 32 (b * t)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (N - t)
  frame : Frame [oR s₀] (P0 s₀).mem s.mem
  out : ∀ j < b * t, s.mem (oA s₀ + BitVec.ofNat 64 j) = (L s₀)[j]!

/-- The end of every branch. -/
structure Fin (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame [oR s₀] (P0 s₀).mem s.mem
  out : ∀ j < 32 * dN s₀, s.mem (oA s₀ + BitVec.ofNat 64 j) = (L s₀)[j]!

theorem Inv.fin {s₀ s : State} {c b N : Nat} (hN : b * N = 32 * dN s₀) (h : Inv s₀ c b N N s) :
    Fin s₀ s := ⟨h.esp, h.rd, h.wr, h.frame, fun j hj => h.out j (by rw [hN]; exact hj)⟩

/-- Coefficient `c t + i` of group `t`, read from `esi`. -/
theorem coef_at {s₀ s : State} (hp : Pre s₀) {c b N t : Nat} (h : Inv s₀ c b N t s) {i : Nat}
    (hi : c * t + i < 256) :
    Coef s i (coeffAt s₀.mem (fA s₀) (c * t + i)).toNat := by
  have ff := hp.f_fit
  have e : s.ea (at_ .esi (4 * i)) = coeffAddr (fA s₀) (c * t + i) := by
    show (s.gpr .esi + BitVec.ofNat 32 (4 * i)).setWidth 64 = _
    rw [h.esi, ea_add (by rw [show 4 * c * t = 4 * (c * t) from Nat.mul_assoc 4 c t]; omega)]
    congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  refine ⟨?_, ?_, hp.f_red _ (by rw [n_eq]; exact hi)⟩
  · rw [e]; exact ⟨polyRegion (fA s₀), by rw [h.rd, h.wr, pushed_rd, P0_wr, hp.rd]; simp,
      coeff_contains _ (by rw [n_eq]; exact hi)⟩
  · rw [e, ← coeffAt_eq, hp.f_keep h.frame hi]

/-- Store a byte of `ebx`/`eax` at `edi + o`: in the output region. -/
theorem out_in {s₀ s : State} (hp : Pre s₀) (hw : s.wr = (P0 s₀).wr) {j : Nat}
    (hj : j < (lenV s₀).toNat) : InRegions s.wr (oA s₀ + BitVec.ofNat 64 j) 1 :=
  ⟨oR s₀, by rw [hw, P0_wr, hp.wr]; simp, contains_at (by omega) hp.o_fit⟩

/-! ## `d` = 1 and 4: a byte of `k` coefficients -/

theorem byte14 {s₀ : State} {d k : Nat} (hd : dN s₀ = d) (hdk : d * k = 8)
    (hd14 : d = 1 ∨ d = 4) {t : Nat} (ht : t < 32 * d) :
    (L s₀)[t]! = BitVec.ofNat 8 (pk d (fun i => C s₀ (k * t + i)) k) := by
  rcases hd14 with rfl | rfl
  · have hk : k = 8 := by omega
    subst hk
    rw [L, hd, compressEncode1 _ (by omega)]
    simp only [pk, C, hd]
    refine congrArg (BitVec.ofNat 8) ?_
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add]
    omega
  · have hk : k = 2 := by omega
    subst hk
    rw [L, hd, compressEncode4 _ (by omega)]
    simp only [pk, C, hd]
    refine congrArg (BitVec.ofNat 8) ?_
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add]
    omega

theorem step14 {s₀ : State} (hp : Pre s₀) {d k N : Nat} (hd : dN s₀ = d) (hdk : d * k = 8)
    (hd14 : d = 1 ∨ d = 4) (hN : N = 32 * d) {t : Nat} (ht : t < N) {s : State}
    (h : Inv s₀ k 1 N t s) :
    WP isa (.block (packBody d k)) s fun s' => Inv s₀ k 1 N (t + 1) s' ∧
      eval .ne s' = some (decide (t + 1 < N)) := by
  have hdm : d ∈ compressWidths := hd ▸ hp.d_mem
  have hk1 : 1 ≤ k := by rcases hd14 with rfl | rfl <;> omega
  have hkt : k * t + k ≤ 256 := by
    rcases hd14 with rfl | rfl
    · have : k = 8 := by omega
      subst this; omega
    · have : k = 2 := by omega
      subst this; omega
  have fo := hp.o_fit
  have hl := hp.len_eq
  have hC : ∀ i < k, C s₀ (k * t + i) = cf d (coeffAt s₀.mem (fA s₀) (k * t + i)).toNat := fun i hi => by
    rw [hp.C_eq (by omega), hd]
  refine ldComp_spec hdm (k - 1) _ s _ (coef_at hp h (i := k - 1) (by omega)) fun s₁ o₁ v₁ => ?_
  refine wp_movr ?_
  have o₂ := o₁.trans (Only.setReg s₁ .ebx (s₁.gpr .eax))
  have bx : ((s₁.setReg .ebx (s₁.gpr .eax)).gpr .ebx).toNat = cf d (coeffAt s₀.mem (fA s₀) (k * t + (k - 1))).toNat := by
    simp only [State.setReg, ite_true]; exact v₁
  refine accSteps_spec hdm (fun i => (coeffAt s₀.mem (fA s₀) (k * t + i)).toNat) (k - 1) _ _ _ _
    (fun i hi => (coef_at hp h (i := i) (by omega)).of_only o₂ (by decide)) bx ?_ fun s₃ o₃ v₃ => ?_
  · have := cf_lt d (coeffAt s₀.mem (fA s₀) (k * t + (k - 1))).toNat
    calc _ ≤ 2 ^ d * 2 ^ (d * (k - 1)) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ 8 := by rw [← Nat.pow_add]; congr 1; rw [← hdk]; rcases hd14 with rfl | rfl <;> omega
      _ ≤ 2 ^ 32 := by decide
  have o := o₂.trans o₃
  have g : ∀ r, r ∉ [Reg.eax, .edx, .ebx] → s₃.gpr r = s.gpr r := fun r hr =>
    o.gpr r (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
  have esi₃ := g .esi (by decide)
  have edi₃ := g .edi (by decide)
  have ecx₃ := g .ecx (by decide)
  have esp₃ := g .esp (by decide)
  have eo : (oP s₀ + BitVec.ofNat 32 t + BitVec.ofNat 32 0).setWidth 64 = oA s₀ + BitVec.ofNat 64 t := by
    rw [ea_add (by omega), Nat.add_zero]
  have out := out_in hp (o.wr.trans h.wr) (j := t) (by omega)
  have ho : 1 * t = t := Nat.one_mul t
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store8, State.setReg, arithFlags, State.setFlags, Reg8.reg,
    Option.bind_some, edi₃, h.edi, ho, eo, out, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  have hbyte : (s₃.gpr .ebx).setWidth 8 = (L s₀)[t]! := by
    rw [setWidth8_eq, v₃, byte14 hd hdk hd14 (by omega), pk_congr (fun i hi => hC i hi)]
    refine congrArg (BitVec.ofNat 8) ?_
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [pk, Nat.add_sub_cancel]
    omega
  refine ⟨⟨by simp [esp₃, h.esp], o.rd.trans h.rd, o.wr.trans h.wr, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide, ite_false, ite_true,
      esi₃, h.esi]
    rw [add_ofNat_add]; congr 2
  · simp only [show Reg.edi ≠ Reg.ecx by decide, ite_false, ite_true, edi₃, h.edi]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]; congr 2; omega
  · simp only [ite_true, ecx₃, h.ecx]
    exact cnt_next ht
  · rw [o.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_at (by omega) fo)
  · rw [o.mem, show 1 * (t + 1) = t + 1 by omega]
    exact bytes_extend1 (by omega) (fun j hj => h.out j (by omega)) hbyte
  · simp only [eval, ecx₃, h.ecx]
    exact cnt_ne ht (by omega)

/-! ## `d` = 10: five bytes of four coefficients -/

theorem step10 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 10) {t : Nat} (ht : t < 64) {s : State}
    (h : Inv s₀ 4 5 64 t s) :
    WP isa (.block pack10Body) s fun s' => Inv s₀ 4 5 64 (t + 1) s' ∧
      eval .ne s' = some (decide (t + 1 < 64)) := by
  have hdm : (10 : Nat) ∈ compressWidths := hd ▸ hp.d_mem
  have fo := hp.o_fit
  have hl := hp.len_eq
  rw [hd] at hl
  have hC : ∀ i < 4, C s₀ (4 * t + i) = cf 10 (coeffAt s₀.mem (fA s₀) (4 * t + i)).toNat := fun i hi => by
    rw [hp.C_eq (by omega), hd]
  refine ldComp_spec hdm 3 _ s _ (coef_at hp h (i := 3) (by omega)) fun s₁ o₁ v₁ => ?_
  refine wp_movr (wp_movr (wp_and fun s₂ o₂ v₂ => ?_))
  have o₃ := (o₁.trans ((Only.setReg s₁ .ebp (s₁.gpr .eax)).trans (Only.setReg _ .ebx _))).trans o₂
  have bx : (s₂.gpr .ebx).toNat = C s₀ (4 * t + 3) % 4 := by
    rw [v₂, show (3 : BitVec 32) = BitVec.ofNat 32 (2 ^ 2 - 1) from rfl, toNat_and_mask _ _ (by decide)]
    simp (config := {decide := true}) only [State.setReg, ite_true, ite_false]
    rw [v₁, hC 3 (by omega)]
  have bp : s₂.gpr .ebp = BitVec.ofNat 32 (C s₀ (4 * t + 3)) := by
    rw [o₂.gpr .ebp (by decide)]
    simp only [State.setReg, ite_true, show Reg.ebp ≠ Reg.ebx by decide, ite_false]
    rw [eq_ofNat_of_toNat v₁, hC 3 (by omega)]
  refine accSteps_spec hdm (fun i => (coeffAt s₀.mem (fA s₀) (4 * t + i)).toNat) 3 _ _ _ _
    (fun i hi => (coef_at hp h (i := i) (by omega)).of_only o₃ (by decide)) bx
    (by have := Nat.mod_lt (C s₀ (4 * t + 3)) (show 4 > 0 by decide); omega) fun s₄ o₄ v₄ => ?_
  have o := o₃.trans o₄
  have g : ∀ r, r ∉ [Reg.eax, .edx, .ebx, .ebp] → s₄.gpr r = s.gpr r := fun r hr =>
    o.gpr r (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
  have esi₄ := g .esi (by decide)
  have edi₄ := g .edi (by decide)
  have ecx₄ := g .ecx (by decide)
  have esp₄ := g .esp (by decide)
  have bp₄ : s₄.gpr .ebp = BitVec.ofNat 32 (C s₀ (4 * t + 3)) := by rw [o₄.gpr .ebp (by decide), bp]
  have eo : ∀ j < 5, (oP s₀ + BitVec.ofNat 32 (5 * t) + BitVec.ofNat 32 j).setWidth 64 =
      oA s₀ + BitVec.ofNat 64 (5 * t + j) := fun j hj => ea_add (by omega)
  have e0 := eo 0 (by omega)
  have e1 := eo 1 (by omega)
  have e2 := eo 2 (by omega)
  have e3 := eo 3 (by omega)
  have e4 := eo 4 (by omega)
  have wr := o.wr.trans h.wr
  have out : ∀ j < 5, InRegions s₄.wr (oA s₀ + BitVec.ofNat 64 (5 * t + j)) 1 :=
    fun j hj => out_in hp wr (by omega)
  have w0 := out 0 (by omega)
  have w1 := out 1 (by omega)
  have w2 := out 2 (by omega)
  have w3 := out 3 (by omega)
  have w4 := out 4 (by omega)
  simp only [Nat.add_zero] at e0 w0
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    execShift, readSrc, State.ea, at_, State.store8, State.setReg, arithFlags, State.setFlags, Reg8.reg,
    Option.bind_some, Option.map_some, edi₄, h.edi, e0, e1, e2, e3, e4, w0, w1, w2, w3, w4, bp₄, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  -- The values.
  have lc : ∀ i < 4, C s₀ (4 * t + i) < 1024 := fun i _ => by rw [C, hd]; exact compress_lt 10 _
  have l0 := lc 0 (by omega)
  rw [Nat.add_zero] at l0
  have l1 := lc 1 (by omega)
  have l2 := lc 2 (by omega)
  have l3 := lc 3 (by omega)
  have hW : (s₄.gpr .ebx).toNat = C s₀ (4 * t) + 1024 * C s₀ (4 * t + 1) +
      1048576 * C s₀ (4 * t + 2) + 1073741824 * (C s₀ (4 * t + 3) % 4) := by
    rw [v₄, pk_congr (cv' := fun i => C s₀ (4 * t + i)) (fun i hi => (hC i (by omega)).symm)]
    simp only [pk, Nat.add_zero]
    omega
  generalize s₄.gpr .ebx = W at hW
  have hb : ∀ j < 4, (W >>> (8 * j)).setWidth 8 = BitVec.ofNat 8 (W.toNat / 2 ^ (8 * j)) := fun j _ => by
    rw [setWidth8_eq, toNat_shr]
  have x0 : W.setWidth 8 = (L s₀)[5 * t]! := by
    rw [setWidth8_eq, L, hd, compressEncode10_0 _ ht]
    exact ofNat8_eq (by simp only [C, hd] at hW l0 l1 l2 l3 ⊢; omega)
  have x1 : (W >>> 8).setWidth 8 = (L s₀)[5 * t + 1]! := by
    rw [setWidth8_eq, toNat_shr, L, hd, compressEncode10_1 _ ht]
    exact ofNat8_eq (by simp only [C, hd, Nat.reducePow] at hW l0 l1 l2 l3 ⊢; omega)
  have x2 : (W >>> 8 >>> 8).setWidth 8 = (L s₀)[5 * t + 2]! := by
    rw [setWidth8_eq, toNat_shr, toNat_shr, L, hd, compressEncode10_2 _ ht]
    exact ofNat8_eq (by simp only [C, hd, Nat.reducePow] at hW l0 l1 l2 l3 ⊢; omega)
  have x3 : (W >>> 8 >>> 8 >>> 8).setWidth 8 = (L s₀)[5 * t + 3]! := by
    rw [setWidth8_eq, toNat_shr, toNat_shr, toNat_shr, L, hd, compressEncode10_3 _ ht]
    exact ofNat8_eq (by simp only [C, hd, Nat.reducePow] at hW l0 l1 l2 l3 ⊢; omega)
  have x4 : (BitVec.ofNat 32 (C s₀ (4 * t + 3)) >>> 2).setWidth 8 = (L s₀)[5 * t + 4]! := by
    rw [setWidth8_eq, toNat_shr, toNat_ofNat32 (by omega), L, hd, compressEncode10_4 _ ht]
    simp only [C, hd]
  clear hb
  refine ⟨⟨by simp [esp₄, h.esp], o.rd.trans h.rd, wr, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide, ite_false, ite_true,
      esi₄, h.esi]
    rw [show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_add]; congr 2
  · simp only [show Reg.edi ≠ Reg.ecx by decide, ite_false, ite_true, edi₄, h.edi]
    rw [show (5 : BitVec 32) = BitVec.ofNat 32 5 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, ecx₄, h.ecx]
    exact cnt_next ht
  · rw [o.mem]
    have c : ∀ j < 5, (oR s₀).Contains (oA s₀ + BitVec.ofNat 64 (5 * t + j)) (8 / 8) :=
      fun j hj => contains_at (by omega) fo
    have c0 := c 0 (by omega)
    simp only [Nat.add_zero] at c0
    exact ((((h.frame.writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _
      (c 1 (by omega))).writeW (List.mem_singleton_self _) _ (c 2 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 3 (by omega))).writeW (List.mem_singleton_self _) _ (c 4 (by omega))
  · rw [o.mem, show 5 * (t + 1) = 5 * t + 4 + 1 by omega]
    refine bytes_extend1 (by omega) ?_ x4
    rw [show 5 * t + 4 = 5 * t + 3 + 1 by omega]
    refine bytes_extend1 (by omega) ?_ x3
    rw [show 5 * t + 3 = 5 * t + 2 + 1 by omega]
    refine bytes_extend1 (by omega) ?_ x2
    rw [show 5 * t + 2 = 5 * t + 1 + 1 by omega]
    refine bytes_extend1 (by omega) ?_ x1
    exact bytes_extend1 (by omega) h.out x0
  · simp only [eval, ecx₄, h.ecx]
    exact cnt_ne ht (by omega)

/-! ## The function -/

/-- After `ceInit`, or the compare with `v`. -/
structure Init (s₀ : State) (v : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = fP s₀
  edi : s.gpr .edi = oP s₀
  eax : s.gpr .eax = dV s₀
  ev : eval .e s = some (decide (dN s₀ = v))

theorem pub_esp {s₀ s₀' : State} (hq : Pub s₀ s₀') : (P0 s₀).gpr .esp = (P0 s₀').gpr .esp := by
  rw [P0_esp, P0_esp, hq.1]

theorem init_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) (Init · 1) (.block ceInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₀ := P0_argAddr s₀ 0
    have a₁ := P0_argAddr s₀ 1
    have a₂ := P0_argAddr s₀ 2
    have i₀ := P0_argIn (s₀ := s₀) (n := 4) (i := 0) (by omega) fit (by simp [hp.wr])
    have i₁ := P0_argIn (s₀ := s₀) (n := 4) (i := 1) (by omega) fit (by simp [hp.wr])
    have i₂ := P0_argIn (s₀ := s₀) (n := 4) (i := 2) (by omega) fit (by simp [hp.wr])
    have v₀ := P0_arg hp.sp (n := 4) (i := 0) (by omega) fit hp.stk_a
    have v₁ := P0_arg hp.sp (n := 4) (i := 1) (by omega) fit hp.stk_a
    have v₂ := P0_arg hp.sp (n := 4) (i := 2) (by omega) fit hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a₀ a₁ a₂
    apply WP.of_runBlock
    simp (config := {decide := true}) only [ceInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a₀, a₁, a₂, i₀, i₁, i₂, v₀, v₁, v₂, ite_true, ite_false,
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

theorem loop_piece {d c b N : Nat} (body : List Instr) (hN : 0 < N)
    (hstep : ∀ t < N, ∀ s₀ s, Pre s₀ → dN s₀ = d → Inv s₀ c b N t s →
      WP isa (.block body) s fun s' => Inv s₀ c b N (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < N)))
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block body) hc).isSome = true) :
    Piece Pre Pub (fun s₀ s => Inv s₀ c b N 0 s ∧ dN s₀ = d) (fun s₀ s => Inv s₀ c b N N s ∧ dN s₀ = d)
      (.loop (.block body) .ne) :=
  Piece.countLoop hN (fun t s₀ s => Inv s₀ c b N t s ∧ dN s₀ = d) [.esp, .esi, .edi, .ecx]
    (fun t ht s₀ s hp ⟨h, hd⟩ => (hstep t ht s₀ s hp hd h).mono fun _ ⟨h', e⟩ => ⟨⟨h', hd⟩, e⟩)
    (fun t _ s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.esp, h'.esp, pub_esp hq]
      · rw [h.esi, h'.esi, fP, fP, hq.2.1]
      · rw [h.edi, h'.edi, oP, oP, hq.2.2.2.1]
      · rw [h.ecx, h'.ecx]) ht

theorem branch_piece {d c b N : Nat} (body : List Instr) (hN : 0 < N) (hbN : b * N = 32 * d)
    (hstep : ∀ t < N, ∀ s₀ s, Pre s₀ → dN s₀ = d → Inv s₀ c b N t s →
      WP isa (.block body) s fun s' => Inv s₀ c b N (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < N)))
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block body) hc).isSome = true)
    {hc' : Taint.Hint VG.X86.Taint.T}
    (ht' : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 N))]) hc').isSome = true) :
    Piece Pre Pub (fun s₀ s => (∃ v, Init s₀ v s) ∧ dN s₀ = d) Fin (countedLoop N body) :=
  (Piece.seq (ecx_piece d c b N ht') (loop_piece body hN hstep ht)).mono (fun _ _ _ h => h)
    fun _ _ _ ⟨h, hd⟩ => h.fin (by rw [hd, hbN])

theorem ite_ev {v : Nat} {P : State → State → Prop} :
    ∀ s₀ s, Pre s₀ → Init s₀ v s ∧ P s₀ s → eval .e s = some (decide (dN s₀ = v)) :=
  fun _ _ _ h => h.1.ev

theorem ite_pub (v : Nat) : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
    decide (dN s₀ = v) = decide (dN s₀' = v) := fun _ _ _ _ hq => by rw [dN, dN, dV, dV, hq.2.2.1]

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Fin
    (.seq (.block ceInit)
      (.ite .e (countedLoop 32 (packBody 1 8))
        (.seq (.block [.alu .cmp .eax (.imm 4)])
          (.ite .e (countedLoop 128 (packBody 4 2)) (countedLoop 64 pack10Body))))) := by
  refine Piece.seq (init_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h, trivial⟩)
    (Piece.ite _ (ite_ev (P := fun _ _ => True)) (ite_pub 1) ?_ ?_)
  · exact (branch_piece (d := 1) (c := 8) (b := 1) (packBody 1 8) (by decide) rfl
      (fun t ht s₀ s hp hd h => step14 hp hd (by decide) (.inl rfl) rfl ht h) (by taint_decide) (by taint_decide)).mono
      (fun _ _ _ ⟨⟨h, _⟩, e⟩ => ⟨⟨1, h⟩, of_decide_eq_true e⟩) fun _ _ _ h => h
  refine Piece.seq (cmp4_piece.mono (fun _ _ _ ⟨⟨h, _⟩, e⟩ => ⟨h, e⟩) fun _ _ _ h => h)
    (Piece.ite _ ite_ev (ite_pub 4) ?_ ?_)
  · exact (branch_piece (d := 4) (c := 2) (b := 1) (packBody 4 2) (by decide) rfl
      (fun t ht s₀ s hp hd h => step14 hp hd (by decide) (.inr rfl) rfl ht h) (by taint_decide) (by taint_decide)).mono
      (fun _ _ _ ⟨⟨h, _⟩, e⟩ => ⟨⟨4, h⟩, of_decide_eq_true e⟩) fun _ _ _ h => h
  · exact (branch_piece (d := 10) (c := 4) (b := 5) pack10Body (by decide) rfl
      (fun t ht s₀ s hp hd h => step10 hp hd ht h) (by taint_decide) (by taint_decide)).mono
      (fun s₀ _ hp ⟨⟨h, h1⟩, e⟩ => ⟨⟨4, h⟩, by
        have := hp.d_mem
        have h4 := of_decide_eq_false e
        rcases mem_compressWidths this with h' | h' | h' <;> [exact absurd h' h1; exact absurd h' h4; exact h']⟩)
      fun _ _ _ h => h

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlKem.X86.compressEncode :=
  Piece.leaf (fun s₀ => [oR s₀]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← hp.stk_eq]; exact hp.stk_o, hp.ret_o⟩)
    (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- Memory with the arguments `0`, `1`, `0x400` and `32` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5008 then 1 else if a = 0x500d then 4 else if a = 0x5010 then 32 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.compressEncode (compressEncodeContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [compressEncodeContract, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [compressEncodeContract, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have hp := Pre.of h₀
    rw [hm, hp.len_eq]
    exact bytesAt_eq! (compressEncode_length _ _) fun j hj => hinv.out j hj
  · let st := satState satMem [⟨0, 1024⟩] [⟨0x400, 32⟩, ⟨0x5004, 16⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 1 := by decide
    have a2 : arg st 2 = 0x400 := by decide
    have a3 : arg st 3 = 32 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [compressEncodeContract, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
      by decide, by decide, reduced_below (fun a ha => ?_) 0 (by decide)⟩
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | (show satMem a = 0
         simp only [satMem]
         rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
           ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
           ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)])

end VG.Proof.MlKem.X86.CompressEncode
