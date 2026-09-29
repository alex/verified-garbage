import VerifiedGarbage.Proof.MlKem.X86.Table
import VerifiedGarbage.Proof.MlKem.X86.NttLoop
import VerifiedGarbage.Proof.MlKem.X86.Red
import VerifiedGarbage.Proof.MlKem.X86.Leaf
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_multiply_ntts`

Untrusted: everything here is checked by Lean. After storing the table of
the `γᵢ` in `scratch` and `h + 1024` in the argument slot of `scratch`, the
loop computes pair `t` of `h` (`multiplyNTTs_even`, `multiplyNTTs_odd`) with
three reductions (`red_spec`) and compares `h + 8(t + 1)` with that end.
-/

namespace VG.Proof.MlKem.X86.Mul

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

section
variable (s₀ : State)
abbrev hP : BitVec 32 := arg s₀ 0
abbrev fP : BitVec 32 := arg s₀ 1
abbrev gP : BitVec 32 := arg s₀ 2
abbrev sP : BitVec 32 := arg s₀ 3
abbrev hA : Addr := (hP s₀).setWidth 64
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev gA : Addr := (gP s₀).setWidth 64
abbrev sA : Addr := (sP s₀).setWidth 64
abbrev aR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
abbrev Fp : Poly := polyAt s₀.mem (fA s₀)
abbrev Gp : Poly := polyAt s₀.mem (gA s₀)
/-- The value of coefficient `i` of `h`. -/
abbrev V (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((multiplyNTTs (Fp s₀) (Gp s₀))[i]!).val
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (fA s₀), polyRegion (gA s₀)]
  wr : s₀.wr = [polyRegion (hA s₀), polyRegion (sA s₀), aR s₀]
  h_f : (polyRegion (hA s₀)).Disjoint (polyRegion (fA s₀))
  h_g : (polyRegion (hA s₀)).Disjoint (polyRegion (gA s₀))
  h_s : (polyRegion (hA s₀)).Disjoint (polyRegion (sA s₀))
  h_a : (polyRegion (hA s₀)).Disjoint (aR s₀)
  f_s : (polyRegion (fA s₀)).Disjoint (polyRegion (sA s₀))
  f_a : (polyRegion (fA s₀)).Disjoint (aR s₀)
  g_s : (polyRegion (gA s₀)).Disjoint (polyRegion (sA s₀))
  g_a : (polyRegion (gA s₀)).Disjoint (aR s₀)
  s_a : (polyRegion (sA s₀)).Disjoint (aR s₀)
  ret_h : (retR s₀).Disjoint (polyRegion (hA s₀))
  ret_f : (retR s₀).Disjoint (polyRegion (fA s₀))
  ret_g : (retR s₀).Disjoint (polyRegion (gA s₀))
  ret_s : (retR s₀).Disjoint (polyRegion (sA s₀))
  ret_a : (retR s₀).Disjoint (aR s₀)
  stk_h : (stkR s₀).Disjoint (polyRegion (hA s₀))
  stk_f : (stkR s₀).Disjoint (polyRegion (fA s₀))
  stk_g : (stkR s₀).Disjoint (polyRegion (gA s₀))
  stk_s : (stkR s₀).Disjoint (polyRegion (sA s₀))
  stk_a : (stkR s₀).Disjoint (aR s₀)
  h_fit : (hP s₀).toNat + 1024 ≤ 2 ^ 32
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32
  g_fit : (gP s₀).toNat + 1024 ≤ 2 ^ 32
  s_fit : (sP s₀).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (fA s₀)
  g_red : Reduced s₀.mem (gA s₀)

theorem Pre.of {s₀ : State} (h : (mulContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧ arg s₀ 3 = arg s₀' 3

theorem pub_esp {s₀ s₀' : State} (hq : Pub s₀ s₀') : (P0 s₀).gpr .esp = (P0 s₀').gpr .esp := by
  rw [P0_esp, P0_esp, hq.1]

/-- The regions the function writes. -/
abbrev W (s₀ : State) : List Region := [polyRegion (hA s₀), polyRegion (sA s₀), aR s₀]

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stk_eq : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem arg_in {i : Nat} (hi : i < 4) : (aR s₀).Contains (argAddr s₀ i) 4 := by
  have := hp.sp'
  simp only [argAddr, Region.Contains, E0] at this ⊢
  bv_omega

theorem in_a {s : State} (hw : s.wr = (P0 s₀).wr) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 :=
  ⟨aR s₀, List.mem_append_right _ (by rw [hw, P0_wr, hp.wr]; simp), hp.arg_in hi⟩

theorem in_w {s : State} (hw : s.wr = (P0 s₀).wr) {r : Region} (hr : r ∈ W s₀) {a : Addr} {n : Nat}
    (hc : r.Contains a n) : InRegions s.wr a n :=
  ⟨r, by rw [hw, P0_wr, hp.wr]; exact List.mem_cons_of_mem _ hr, hc⟩

theorem in_r {s : State} (hr' : s.rd = (P0 s₀).rd) {r : Region} (hr : r ∈ [polyRegion (fA s₀), polyRegion (gA s₀)])
    {a : Addr} {n : Nat} (hc : r.Contains a n) : InRegions (s.rd ++ s.wr) a n :=
  ⟨r, List.mem_append_left _ (by rw [hr', pushed_rd, hp.rd]; exact hr), hc⟩

/-- The push changes nothing but its frame. -/
theorem P0_keep : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf
  exact hf

/-- `f` and `g` keep their values. -/
theorem keep {m : Mem} (hf : Frame (W s₀) (P0 s₀).mem m) {p : Addr}
    (hd : ∀ r ∈ frameR s₀ :: W s₀, (polyRegion p).Disjoint r) {i : Nat} (hi : i < 256) :
    coeffAt m p i = coeffAt s₀.mem p i :=
  coeffAt_congr (fun j hj => bytes_frame ((hp.P0_keep.mono (by simp)).trans (hf.mono (by simp))) hd
    (by decide) j hj) (by rw [n_eq]; exact hi)

theorem f_keep {m : Mem} (hf : Frame (W s₀) (P0 s₀).mem m) {i : Nat} (hi : i < 256) :
    coeffAt m (fA s₀) i = coeffAt s₀.mem (fA s₀) i := by
  refine hp.keep hf (fun r hr => ?_) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [← hp.stk_eq]; exact hp.stk_f.symm
  · exact hp.h_f.symm
  · exact hp.f_s
  · exact hp.f_a

theorem g_keep {m : Mem} (hf : Frame (W s₀) (P0 s₀).mem m) {i : Nat} (hi : i < 256) :
    coeffAt m (gA s₀) i = coeffAt s₀.mem (gA s₀) i := by
  refine hp.keep hf (fun r hr => ?_) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [← hp.stk_eq]; exact hp.stk_g.symm
  · exact hp.h_g.symm
  · exact hp.g_s
  · exact hp.g_a

end Pre

/-- After `t` pairs. -/
structure MI (s₀ : State) (t : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  ebx : s.gpr .ebx = hP s₀ + BitVec.ofNat 32 (8 * t)
  esi : s.gpr .esi = fP s₀ + BitVec.ofNat 32 (8 * t)
  edi : s.gpr .edi = gP s₀ + BitVec.ofNat 32 (8 * t)
  ebp : s.gpr .ebp = sP s₀ + BitVec.ofNat 32 (4 * t)
  frame : Frame (W s₀) (P0 s₀).mem s.mem
  tbl : ∀ k < 128, coeffAt s.mem (sA s₀) k = BitVec.ofNat 32 (gammas.getD k 0)
  slot : s.mem.readW (argAddr s₀ 3) 32 = hP s₀ + 1024
  out : ∀ i < 2 * t, coeffAt s.mem (hA s₀) i = V s₀ i

theorem mul_even (a b c d γ : Zq) :
    (a * b + c * d * γ).val = (a.val * b.val + (c.val * d.val % q) * γ.val) % q := by
  rw [val_add', val_mul, val_mul, val_mul]
  simp only [Nat.add_mod_mod, Nat.mod_add_mod]

theorem gamma_val {t : Nat} (ht : t < 128) : (gamma t).val = gammas.getD t 0 := (gammas_getD ht).symm

theorem mul_odd (a b c d : Zq) : (a * d + c * b).val = (a.val * d.val + c.val * b.val) % q := by
  rw [val_add', val_mul, val_mul, ← Nat.add_mod]

theorem mul_step {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < 128) {s : State} (h : MI s₀ t s) :
    WP isa (.block mulBody) s fun s' => MI s₀ (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < 128)) := by
  have hf := hp.f_fit
  have hg := hp.g_fit
  have hh := hp.h_fit
  have hs := hp.s_fit
  have i0 : 2 * t < n := by rw [n_eq]; omega
  have i1 : 2 * t + 1 < n := by rw [n_eq]; omega
  have it : t < n := by rw [n_eq]; omega
  -- The addresses.
  have ea_f0 : (s.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (fA s₀) (2 * t) := by
    rw [h.esi, ea_add (by omega)]; congr 2; omega
  have ea_f1 : (s.gpr .esi + BitVec.ofNat 32 4).setWidth 64 = coeffAddr (fA s₀) (2 * t + 1) := by
    rw [h.esi, ea_add (by omega)]; congr 2; omega
  have ea_g0 : (s.gpr .edi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (gA s₀) (2 * t) := by
    rw [h.edi, ea_add (by omega)]; congr 2; omega
  have ea_g1 : (s.gpr .edi + BitVec.ofNat 32 4).setWidth 64 = coeffAddr (gA s₀) (2 * t + 1) := by
    rw [h.edi, ea_add (by omega)]; congr 2; omega
  have ea_z : (s.gpr .ebp + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (sA s₀) t := by
    rw [h.ebp, ea_add (by omega), Nat.add_zero]
  have ea_h0 : (s.gpr .ebx + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (hA s₀) (2 * t) := by
    rw [h.ebx, ea_add (by omega)]; congr 2; omega
  have ea_h1 : (s.gpr .ebx + BitVec.ofNat 32 4).setWidth 64 = coeffAddr (hA s₀) (2 * t + 1) := by
    rw [h.ebx, ea_add (by omega)]; congr 2; omega
  have ea_sl : (s.gpr .esp + BitVec.ofNat 32 32).setWidth 64 = argAddr s₀ 3 := by
    rw [h.esp]; exact P0_argAddr s₀ 3
  -- The permissions.
  have in_f0 := hp.in_r h.rd (List.mem_cons_self ..) (coeff_contains (fA s₀) i0)
  have in_f1 := hp.in_r h.rd (List.mem_cons_self ..) (coeff_contains (fA s₀) i1)
  have in_g0 := hp.in_r h.rd (by simp) (coeff_contains (gA s₀) i0)
  have in_g1 := hp.in_r h.rd (by simp) (coeff_contains (gA s₀) i1)
  have in_z : InRegions (s.rd ++ s.wr) (coeffAddr (sA s₀) t) 4 :=
    inRd (hp.in_w h.wr (by simp) (coeff_contains (sA s₀) it))
  have in_h0 : InRegions s.wr (coeffAddr (hA s₀) (2 * t)) 4 := hp.in_w h.wr (by simp) (coeff_contains _ i0)
  have in_h1 : InRegions s.wr (coeffAddr (hA s₀) (2 * t + 1)) 4 := hp.in_w h.wr (by simp) (coeff_contains _ i1)
  have in_sl := hp.in_a h.wr (i := 3) (by decide)
  -- The values.
  have vf0 := hp.f_keep h.frame (i := 2 * t) (by omega)
  have vf1 := hp.f_keep h.frame (i := 2 * t + 1) (by omega)
  have vg0 := hp.g_keep h.frame (i := 2 * t) (by omega)
  have vg1 := hp.g_keep h.frame (i := 2 * t + 1) (by omega)
  have vz := h.tbl t ht
  rw [coeffAt_eq] at vf0 vf1 vg0 vg1 vz
  have lf0 := hp.f_red (2 * t) i0
  have lf1 := hp.f_red (2 * t + 1) i1
  have lg0 := hp.g_red (2 * t) i0
  have lg1 := hp.g_red (2 * t + 1) i1
  have lz : gammas.getD t 0 < q := by rw [gammas_getD ht]; exact (gamma t).isLt
  have pf0 := polyAt_val hp.f_red i0
  have pf1 := polyAt_val hp.f_red i1
  have pg0 := polyAt_val hp.g_red i0
  have pg1 := polyAt_val hp.g_red i1
  generalize coeffAt s₀.mem (fA s₀) (2 * t) = F0 at vf0 lf0 pf0
  generalize coeffAt s₀.mem (fA s₀) (2 * t + 1) = F1 at vf1 lf1 pf1
  generalize coeffAt s₀.mem (gA s₀) (2 * t) = G0 at vg0 lg0 pg0
  generalize coeffAt s₀.mem (gA s₀) (2 * t + 1) = G1 at vg1 lg1 pg1
  rw [q_eq] at lf0 lf1 lg0 lg1 lz
  have p11 : F1.toNat * G1.toNat < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lf1 lg1; omega
  rw [mulBody, WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execMul,
    readSrc, State.ea, at_, State.load32, State.setReg, State.setFlags, Option.map_some, ea_f1, ea_g1,
    in_f1, in_g1, vf1, vg1, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine red_spec (r := .ecx) (by decide) (by decide) _ _ _ (x := F1.toNat * G1.toNat)
    (by simp only [ite_true, ite_false, reduceCtorEq]; exact toNat_ofNat32 p11)
    (by simp only [ite_true, ite_false, reduceCtorEq]; exact toNat_ofNat32 p11) fun s₁ o₁ v₁ => ?_
  have g₁ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ecx → s₁.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₁.gpr r (by simp [h1, h2, h3])]; simp [h1, h2, h3]
  have esi₁ := g₁ .esi (by decide) (by decide) (by decide)
  have edi₁ := g₁ .edi (by decide) (by decide) (by decide)
  have ebp₁ := g₁ .ebp (by decide) (by decide) (by decide)
  have m₁ : s₁.mem = s.mem := o₁.mem
  have rd₁ : s₁.rd = s.rd := o₁.rd
  have wr₁ : s₁.wr = s.wr := o₁.wr
  have cx₁ : s₁.gpr .ecx = BitVec.ofNat 32 (F1.toNat * G1.toNat % q) := eq_ofNat_of_toNat v₁
  have lr₁ := Nat.mod_lt (F1.toNat * G1.toNat) (show q > 0 by rw [q_eq]; decide)
  rw [q_eq] at lr₁
  have hzv : (BitVec.ofNat 32 (gammas.getD t 0)).toNat = gammas.getD t 0 := toNat_ofNat32 (by omega)
  have x2 : F1.toNat * G1.toNat % q * gammas.getD t 0 + F0.toNat * G0.toNat < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lr₁ lz
    have := Nat.mul_lt_mul_of_lt_of_lt lf0 lg0
    rw [q_eq]; omega
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execMul,
    readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    Option.map_some, esi₁, edi₁, ebp₁, cx₁, m₁, rd₁, wr₁, ea_z, ea_f0, ea_g0, in_z, in_f0, in_g0, vz, vf0,
    vg0, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  have p00 : F0.toNat * G0.toNat < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lf0 lg0; omega
  have ev2 : (BitVec.ofNat 32 ((BitVec.ofNat 32 (F1.toNat * G1.toNat % q)).toNat *
      (BitVec.ofNat 32 (gammas.getD t 0)).toNat) + BitVec.ofNat 32 (F0.toNat * G0.toNat)).toNat =
      F1.toNat * G1.toNat % q * gammas.getD t 0 + F0.toNat * G0.toNat := by
    rw [toNat_ofNat32 (n := F1.toNat * G1.toNat % q) (by rw [q_eq]; omega), hzv, BitVec.toNat_add,
      toNat_ofNat32 (by omega), toNat_ofNat32 p00, Nat.mod_eq_of_lt x2]
  refine red_spec (r := .ecx) (by decide) (by decide) _ _ _
    (x := F1.toNat * G1.toNat % q * gammas.getD t 0 + F0.toNat * G0.toNat)
    (by simp only [ite_true, ite_false, reduceCtorEq]; exact ev2)
    (by simp only [ite_true, ite_false, reduceCtorEq]; exact ev2) fun s₂ o₂ v₂ => ?_
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ecx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3])]; simp [h1, h2, h3, g₁]
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have edi₂ := g₂ .edi (by decide) (by decide) (by decide)
  have ebx₂ := g₂ .ebx (by decide) (by decide) (by decide)
  have m₂ : s₂.mem = s.mem := o₂.mem
  have rd₂ : s₂.rd = s.rd := o₂.rd
  have wr₂ : s₂.wr = s.wr := o₂.wr
  have cx₂ : s₂.gpr .ecx = BitVec.ofNat 32 ((F1.toNat * G1.toNat % q * gammas.getD t 0 +
      F0.toNat * G0.toNat) % q) := eq_ofNat_of_toNat v₂
  have sep : ∀ {p : Addr} {j : Nat}, (polyRegion p).Disjoint (polyRegion (hA s₀)) → j < n →
      ∀ V : BitVec 32, (s.mem.writeW (coeffAddr (hA s₀) (2 * t)) V).readW (coeffAddr p j) 32 =
        s.mem.readW (coeffAddr p j) 32 := fun hd hj V =>
    Mem.readW_writeW_sep (hd.sep (coeff_contains _ hj) (coeff_contains _ i0)) (by decide)
  have wf0 := sep hp.h_f.symm i0
  have wf1 := sep hp.h_f.symm i1
  have wg0 := sep hp.h_g.symm i0
  have wg1 := sep hp.h_g.symm i1
  have p01 : F0.toNat * G1.toNat < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lf0 lg1; omega
  have p10 : F1.toNat * G0.toNat < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lf1 lg0; omega
  have x3 : F0.toNat * G1.toNat + F1.toNat * G0.toNat < 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lf0 lg1
    have := Nat.mul_lt_mul_of_lt_of_lt lf1 lg0
    omega
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execMul,
    readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, Option.map_some, esi₂, edi₂, ebx₂, cx₂, m₂, rd₂, wr₂, ea_h0, ea_f0, ea_g0, ea_f1,
    ea_g1, in_h0, in_f0, in_g0, in_f1, in_g1, wf0, wf1, wg0, wg1, vf0, vg0, vf1, vg1, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  have ev3 : (BitVec.ofNat 32 (F0.toNat * G1.toNat) + BitVec.ofNat 32 (F1.toNat * G0.toNat)).toNat =
      F0.toNat * G1.toNat + F1.toNat * G0.toNat := by
    rw [BitVec.toNat_add, toNat_ofNat32 p01, toNat_ofNat32 p10, Nat.mod_eq_of_lt x3]
  refine red_spec (r := .ecx) (by decide) (by decide) _ _ _ (x := F0.toNat * G1.toNat + F1.toNat * G0.toNat)
    (by simp only [ite_true, ite_false, reduceCtorEq]; exact ev3)
    (by simp only [ite_true, ite_false, reduceCtorEq]; exact ev3) fun s₃ o₃ v₃ => ?_
  have g₃ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ecx → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₃.gpr r (by simp [h1, h2, h3])]; simp [h1, h2, h3, g₂]
  have esi₃ := g₃ .esi (by decide) (by decide) (by decide)
  have edi₃ := g₃ .edi (by decide) (by decide) (by decide)
  have ebx₃ := g₃ .ebx (by decide) (by decide) (by decide)
  have ebp₃ := g₃ .ebp (by decide) (by decide) (by decide)
  have esp₃ := g₃ .esp (by decide) (by decide) (by decide)
  have m₃ := o₃.mem
  have rd₃ : s₃.rd = s.rd := o₃.rd
  have wr₃ : s₃.wr = s.wr := o₃.wr
  have cx₃ : s₃.gpr .ecx = BitVec.ofNat 32 ((F0.toNat * G1.toNat + F1.toNat * G0.toNat) % q) :=
    eq_ofNat_of_toNat v₃
  generalize eH0 : BitVec.ofNat 32 ((F1.toNat * G1.toNat % q * gammas.getD t 0 + F0.toNat * G0.toNat) % q) = H0
    at m₃
  have sl₂ : ∀ V₀ V₁ : BitVec 32, ((s.mem.writeW (coeffAddr (hA s₀) (2 * t)) V₀).writeW
      (coeffAddr (hA s₀) (2 * t + 1)) V₁).readW (argAddr s₀ 3) 32 = hP s₀ + 1024 := fun V₀ V₁ => by
    rw [Mem.readW_writeW_sep (hp.h_a.symm.sep (hp.arg_in (by decide)) (coeff_contains _ i1)) (by decide),
      Mem.readW_writeW_sep (hp.h_a.symm.sep (hp.arg_in (by decide)) (coeff_contains _ i0)) (by decide),
      h.slot]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, esi₃, edi₃, ebx₃, ebp₃, esp₃, cx₃, m₃, rd₃, wr₃, ea_h1, ea_sl, in_h1, in_sl, sl₂,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  have v0 : H0 = V s₀ (2 * t) := by
    rw [← eH0, V, multiplyNTTs_even _ _ ht, mul_even, pf0, pg0, pf1, pg1, gamma_val ht, Nat.add_comm]
  have v1 : BitVec.ofNat 32 ((F0.toNat * G1.toNat + F1.toNat * G0.toNat) % q) = V s₀ (2 * t + 1) := by
    rw [V, multiplyNTTs_odd _ _ ht, mul_odd, pf0, pg0, pf1, pg1]
  have hsep : ∀ {k : Nat}, k < 128 → ∀ j, j < n → Mem.Sep (coeffAddr (sA s₀) k) 4 (coeffAddr (hA s₀) j) 4 :=
    fun hk j hj => hp.h_s.symm.sep (coeff_contains _ (by rw [n_eq]; omega)) (coeff_contains _ hj)
  refine ⟨⟨by simp [esp₃, h.esp], h.rd, h.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [ite_true, show Reg.ebx ≠ Reg.ebp by decide, show Reg.ebx ≠ Reg.edi by decide,
      show Reg.ebx ≠ Reg.esi by decide, ite_false, h.ebx]
    rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, show Reg.esi ≠ Reg.ebp by decide, show Reg.esi ≠ Reg.edi by decide, ite_false, h.esi]
    rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, show Reg.edi ≠ Reg.ebp by decide, ite_false, h.edi]
    rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ebp]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · exact (h.frame.writeW (by simp) _ (coeff_contains _ i0)).writeW (by simp) _ (coeff_contains _ i1)
  · intro k hk
    rw [coeffAt_writeW_sep _ _ _ (hsep hk _ i1), coeffAt_writeW_sep _ _ _ (hsep hk _ i0)]
    exact h.tbl k hk
  · exact sl₂ _ _
  · intro i hi
    rw [coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) i1,
      coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) i0]
    by_cases e1 : 2 * t + 1 = i
    · rw [ite_eq_left e1, ← e1, v1]
    rw [ite_eq_right e1]
    by_cases e0 : 2 * t = i
    · rw [ite_eq_left e0, ← e0, v0]
    rw [ite_eq_right e0]
    exact h.out i (by omega)
  · simp only [eval, Option.map_some, h.ebx]
    rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_add, NttLoop.end_cmp _ (by omega)]
    by_cases e : t + 1 = 128
    · simp [e, show 8 * t = 1016 by omega]
    · simp only [show ¬ 8 * t + 8 = 1024 by omega, decide_false, Bool.not_false]
      simp only [Option.some.injEq]; exact (decide_eq_true (by omega)).symm

/-! ## The function -/

theorem arg_sep {s₀ : State} (hp : Pre s₀) {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) :
    Mem.Sep (argAddr s₀ i) 4 (argAddr s₀ j) 4 := by
  have := hp.sp'
  intro x h₁ h₂
  simp only [argAddr, E0] at this h₁ h₂
  have : i < j ∨ j < i := by omega
  bv_omega

/-- After `mulLd`. -/
structure S1 (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  eax : s.gpr .eax = sP s₀

theorem ld_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) S1 (.block mulLd) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₃ := P0_argAddr s₀ 3
    have i₃ := P0_argIn (s₀ := s₀) (n := 4) (i := 3) (by omega) fit (by simp [hp.wr])
    have v₃ := P0_arg hp.sp (n := 4) (i := 3) (by omega) fit (by simpa [← hp.stk_eq] using hp.stk_a)
    simp only [Nat.reduceMul, Nat.reduceAdd] at a₃
    apply WP.of_runBlock
    simp only [mulLd, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea,
      State.load32, State.setReg, Option.map_some, a₃, i₃, v₃, ite_true, Option.some.injEq,
      exists_eq_left']
    exact ⟨by simp, rfl, rfl, rfl, by simp⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', pub_esp hq]

theorem setup_piece : Piece Pre Pub S1 (MI · 0) (.block mulSetup) := by
  refine Piece.taint [.esp, .eax] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · have fs := hp.s_fit
    have fit := hp.sp'
    rw [mulSetup]
    refine table_spec gammaTable (b := .eax) (by decide) (p := sA s₀) _ s _
      (fun k hk => by
        show (s.gpr .eax + BitVec.ofNat 32 (4 * k)).setWidth 64 = _
        rw [h.eax, ea_off (by omega)])
      (fun k hk => hp.in_w h.wr (by simp) (coeff_contains _ (by rw [n_eq]; omega))) fun s₁ o₁ f₁ c₁ => ?_
    have esp₁ : s₁.gpr .esp = (P0 s₀).gpr .esp := by rw [o₁.gpr .esp (by decide), h.esp]
    have eax₁ : s₁.gpr .eax = sP s₀ := by rw [o₁.gpr .eax (by decide), h.eax]
    have wr₁ : s₁.wr = (P0 s₀).wr := o₁.wr.trans h.wr
    have rd₁ : s₁.rd = (P0 s₀).rd := o₁.rd.trans h.rd
    have ad : ∀ i, (s₁.gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i := fun i => by
      rw [esp₁]; exact P0_argAddr s₀ i
    have a20 := ad 0
    have a24 := ad 1
    have a28 := ad 2
    have a32 := ad 3
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a20 a24 a28 a32
    have ins : ∀ i < 4, InRegions (s₁.rd ++ s₁.wr) (argAddr s₀ i) 4 := fun i hi => hp.in_a wr₁ hi
    have in0 := ins 0 (by decide)
    have in1 := ins 1 (by decide)
    have in2 := ins 2 (by decide)
    have in3 : InRegions s₁.wr (argAddr s₀ 3) 4 := hp.in_w wr₁ (by simp) (hp.arg_in (by decide))
    have hsa : ∀ i < 4, ∀ r ∈ [polyRegion (sA s₀)], (⟨argAddr s₀ i, 4⟩ : Region).Disjoint r := by
      intro i hi r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.s_a.symm.sub_left (sub_of_contains (hp.arg_in hi))
    have va : ∀ i < 4, s₁.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
      rw [f₁.readW (Region.contains_self _ _) (hsa i hi) (by decide), h.mem]
      exact P0_arg hp.sp (n := 4) (i := i) hi fit (by simpa [← hp.stk_eq] using hp.stk_a)
    have v0 := va 0 (by decide)
    have v1 := va 1 (by decide)
    have v2 := va 2 (by decide)
    have w1 : ∀ V : BitVec 32, (s₁.mem.writeW (argAddr s₀ 3) V).readW (argAddr s₀ 1) 32 = arg s₀ 1 :=
      fun V => by rw [Mem.readW_writeW_sep (arg_sep hp (by decide) (by decide) (by decide)) (by decide), v1]
    have w2 : ∀ V : BitVec 32, (s₁.mem.writeW (argAddr s₀ 3) V).readW (argAddr s₀ 2) 32 = arg s₀ 2 :=
      fun V => by rw [Mem.readW_writeW_sep (arg_sep hp (by decide) (by decide) (by decide)) (by decide), v2]
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.ea, at_, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a20, a24, a28, a32, in0, in1, in2, in3, v0, w1, w2, ite_true,
      ite_false, Option.some.injEq, exists_eq_left']
    have hs1 : Frame [polyRegion (sA s₀)] (P0 s₀).mem s₁.mem := h.mem ▸ f₁
    refine ⟨by simp [esp₁], rd₁, wr₁, by simp, by simp, by simp, by simp [eax₁], ?_, ?_, ?_,
      fun i hi => absurd hi (by omega)⟩
    · exact (hs1.mono (by simp)).writeW (by simp) _ (hp.arg_in (by decide))
    · intro k hk
      rw [coeffAt_writeW_sep _ _ _ (hp.s_a.sep (coeff_contains _ (by rw [n_eq]; omega)) (hp.arg_in (by decide))),
        c₁ k hk]
      rfl
    · exact Mem.readW_writeW_self32 _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.esp, h'.esp, pub_esp hq]
    · rw [h.eax, h'.eax, sP, sP, hq.2.2.2.2]

theorem loop_piece : Piece Pre Pub (MI · 0) (MI · 128) (.loop (.block mulBody) .ne) :=
  Piece.countLoop (by decide) (fun t s₀ s => MI s₀ t s) [.esp, .ebx, .esi, .edi, .ebp]
    (fun t ht s₀ s hp h => mul_step hp ht h)
    (fun t _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.esp, h'.esp, pub_esp hq]
      · rw [h.ebx, h'.ebx, hP, hP, hq.2.1]
      · rw [h.esi, h'.esi, fP, fP, hq.2.2.1]
      · rw [h.edi, h'.edi, gP, gP, hq.2.2.2.1]
      · rw [h.ebp, h'.ebp, sP, sP, hq.2.2.2.2]) (by taint_decide)

theorem hW {s₀ : State} (hp : Pre s₀) : ∀ r ∈ W s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by rw [← hp.stk_eq]; exact hp.stk_h, hp.ret_h⟩
  · exact ⟨by rw [← hp.stk_eq]; exact hp.stk_s, hp.ret_s⟩
  · exact ⟨by rw [← hp.stk_eq]; exact hp.stk_a, hp.ret_a⟩

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (MI s₀ 128) s₀ s')
    Impl.MlKem.X86.multiplyNTTs :=
  Piece.leaf W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp => hW hp) (fun _ _ _ _ hq => hq.1)
    ((Piece.seq ld_piece (Piece.seq setup_piece loop_piece)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- Memory with the arguments `0`, `0x400`, `0x800` and `0xc00` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 4 else if a = 0x500d then 8 else if a = 0x5011 then 0xc else 0

theorem verified : Verified X86.target Impl.MlKem.X86.multiplyNTTs (mulContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact polyIs_of_coeffAt fun i hi => hinv.out i (by rw [n_eq] at hi; omega)
  · let st := satState satMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0xc00, 1024⟩, ⟨0x5004, 16⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 0x400 := by decide
    have a2 : arg st 2 = 0x800 := by decide
    have a3 : arg st 3 = 0xc00 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    have esp : st.gpr .esp = 0x5000 := rfl
    refine ⟨st, ?_⟩
    sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e, esp]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, by decide, by decide, by decide, by decide, reduced_below (fun a ha => ?_) 0x400 (by decide),
      reduced_below (fun a ha => ?_) 0x800 (by decide)⟩
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | (show satMem a = 0
         simp only [satMem]
         rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
           ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
           ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)])

end VG.Proof.MlKem.X86.Mul
