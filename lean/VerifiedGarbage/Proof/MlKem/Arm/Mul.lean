import VerifiedGarbage.Proof.MlKem.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_multiply_ntts`

Untrusted: everything here is checked by Lean. The registers saved and the
table of the `γᵢ` stored (`setup_ok`); then one pair of coefficients per
iteration (`multiplyNTTs_even`, `multiplyNTTs_odd`), whose body is
symbolically executed once for any pointers (`body_ok`); the invariant
says which coefficients of `h` are written, and that `h` is the only
memory written since the setup (`Inv`); then the registers restored.
-/

namespace VG.Proof.MlKem.Arm.Mul

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## Values -/

theorem red_mac (x y z w : Zq) :
    red C (BitVec.ofNat 32 x.val * BitVec.ofNat 32 y.val + BitVec.ofNat 32 z.val * BitVec.ofNat 32 w.val) =
      BitVec.ofNat 32 (x * y + z * w).val := by
  have hx := val_lt x
  have hy := val_lt y
  have hz := val_lt z
  have hw := val_lt w
  have p1 := mul_lt_q2 hx hy
  have p2 := mul_lt_q2 hz hw
  have hs : (BitVec.ofNat 32 x.val * BitVec.ofNat 32 y.val + BitVec.ofNat 32 z.val * BitVec.ofNat 32 w.val).toNat =
      x.val * y.val + z.val * w.val := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x.val) (by omega),
      Nat.mod_eq_of_lt (a := y.val) (by omega), Nat.mod_eq_of_lt (a := z.val) (by omega),
      Nat.mod_eq_of_lt (a := w.val) (by omega), Nat.mod_eq_of_lt (a := x.val * y.val) (by omega),
      Nat.mod_eq_of_lt (a := z.val * w.val) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  refine ofNat_val_eq ?_
  rw [red_toNat (by rw [hs]; omega), hs, val_add', val_mul, val_mul, ← Nat.add_mod]

theorem even_eq (a b c d γ : Zq) :
    red C (BitVec.ofNat 32 a.val * BitVec.ofNat 32 b.val +
      red C (BitVec.ofNat 32 c.val * BitVec.ofNat 32 d.val) * BitVec.ofNat 32 γ.val) =
      BitVec.ofNat 32 (a * b + c * d * γ).val := by
  rw [red_mul]; exact red_mac a b (c * d) γ

/-! ## The loop body -/

section
variable {s : State} {x0 x1 x2 x3 c : BitVec 32}

theorem body_ok (h0 : s.gpr .r0 = x0) (h1 : s.gpr .r1 = x1) (h2 : s.gpr .r2 = x2) (h3 : s.gpr .r3 = x3)
    (h8 : s.gpr .r8 = C) (h11 : s.gpr .r11 = c)
    (if0 : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 0)) 4)
    (if1 : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 4)) 4)
    (ig0 : InRegions (s.rd ++ s.wr) (State.addr (x2 + BitVec.ofNat 32 0)) 4)
    (ig1 : InRegions (s.rd ++ s.wr) (State.addr (x2 + BitVec.ofNat 32 4)) 4)
    (iγ : InRegions (s.rd ++ s.wr) (State.addr (x3 + BitVec.ofNat 32 0)) 4)
    (o0 : InRegions s.wr (State.addr (x0 + BitVec.ofNat 32 0)) 4)
    (o1 : InRegions s.wr (State.addr (x0 + BitVec.ofNat 32 4)) 4) :
    WP isa (.block mulBody) s fun s' =>
      s'.gpr .r0 = x0 + 8 ∧ s'.gpr .r1 = x1 + 8 ∧ s'.gpr .r2 = x2 + 8 ∧ s'.gpr .r3 = x3 + 4 ∧
      s'.gpr .r8 = C ∧ s'.gpr .r11 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ s'.gpr .lr = s.gpr .lr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW (State.addr (x0 + BitVec.ofNat 32 0))
          (red C (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 *
              s.mem.readW (State.addr (x2 + BitVec.ofNat 32 0)) 32 +
            red C (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 4)) 32 *
              s.mem.readW (State.addr (x2 + BitVec.ofNat 32 4)) 32) *
            s.mem.readW (State.addr (x3 + BitVec.ofNat 32 0)) 32))).writeW
        (State.addr (x0 + BitVec.ofNat 32 4))
          (red C (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32 *
              s.mem.readW (State.addr (x2 + BitVec.ofNat 32 4)) 32 +
            s.mem.readW (State.addr (x1 + BitVec.ofNat 32 4)) 32 *
              s.mem.readW (State.addr (x2 + BitVec.ofNat 32 0)) 32)) := by
  run_block [mulBody, reduce, barrett, subQ, fixup, red, bar, fixq, h0, h1, h2, h3, h8, h11, if0, if1, ig0,
    ig1, iγ, o0, o1, and_self, and_true]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev ph : BitVec 32 := s₀.gpr .r0
abbrev pf : BitVec 32 := s₀.gpr .r1
abbrev pg : BitVec 32 := s₀.gpr .r2
abbrev ps : BitVec 32 := s₀.gpr .r3
abbrev H : Addr := State.addr (ph s₀)
abbrev F : Addr := State.addr (pf s₀)
abbrev G : Addr := State.addr (pg s₀)
abbrev S : Addr := State.addr (ps s₀)
abbrev fp : Poly := polyAt s₀.mem (F s₀)
abbrev gp : Poly := polyAt s₀.mem (G s₀)

/-- Coefficient `j` of the output. -/
def out (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((multiplyNTTs (fp s₀) (gp s₀))[j]!).val

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (F s₀), polyRegion (G s₀)]
  wr : s₀.wr = [polyRegion (H s₀), polyRegion (S s₀)]
  hf : (polyRegion (H s₀)).Disjoint (polyRegion (F s₀))
  hg : (polyRegion (H s₀)).Disjoint (polyRegion (G s₀))
  hs : (polyRegion (H s₀)).Disjoint (polyRegion (S s₀))
  fs : (polyRegion (F s₀)).Disjoint (polyRegion (S s₀))
  gs : (polyRegion (G s₀)).Disjoint (polyRegion (S s₀))
  fitH : (ph s₀).toNat + 1024 ≤ 2 ^ 32
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitG : (pg s₀).toNat + 1024 ≤ 2 ^ 32
  fitS : (ps s₀).toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s₀.mem (F s₀)
  redG : Reduced s₀.mem (G s₀)

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  sav : Saved m₁ (S s₀ + BitVec.ofNat 64 512) s₀.gpr
  tab : ∀ j < 128, m₁.readW (S s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (gammaTable.getD j 0)
  f : ∀ j < 256, coeffAt m₁ (F s₀) j = coeffAt s₀.mem (F s₀) j
  g : ∀ j < 256, coeffAt m₁ (G s₀) j = coeffAt s₀.mem (G s₀) j

/-- After `i` pairs, from the memory `m₁` the setup left. -/
structure Inv (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = ph s₀ + BitVec.ofNat 32 (8 * i)
  r1 : s.gpr .r1 = pf s₀ + BitVec.ofNat 32 (8 * i)
  r2 : s.gpr .r2 = pg s₀ + BitVec.ofNat 32 (8 * i)
  r3 : s.gpr .r3 = ps s₀ + BitVec.ofNat 32 (4 * i)
  r8 : s.gpr .r8 = C
  r11 : s.gpr .r11 = BitVec.ofNat 32 (1 * (128 - i))
  lr : s.gpr .lr = s₀.gpr .lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion (H s₀)] m₁ s.mem
  coeff : ∀ j < 256, coeffAt s.mem (H s₀) j = if j < 2 * i then out s₀ j else coeffAt m₁ (H s₀) j

theorem out_even (s₀ : State) {i : Nat} (hi : i < 128) :
    out s₀ (2 * i) = BitVec.ofNat 32 ((fp s₀)[2 * i]! * (gp s₀)[2 * i]! +
      (fp s₀)[2 * i + 1]! * (gp s₀)[2 * i + 1]! * gamma i).val := by
  rw [out, multiplyNTTs_even _ _ hi]

theorem out_odd (s₀ : State) {i : Nat} (hi : i < 128) :
    out s₀ (2 * i + 1) = BitVec.ofNat 32 ((fp s₀)[2 * i]! * (gp s₀)[2 * i + 1]! +
      (fp s₀)[2 * i + 1]! * (gp s₀)[2 * i]!).val := by
  rw [out, multiplyNTTs_odd _ _ hi]

theorem step {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {i : Nat} (hi : i < 128) {s : State}
    (h : Inv s₀ m₁ i s) :
    WP isa (.block mulBody) s fun s' => Inv s₀ m₁ (i + 1) s' ∧ s'.z = decide (i + 1 = 128) := by
  have fH := hp.fitH
  have fF := hp.fitF
  have fG := hp.fitG
  have fS := hp.fitS
  have eF0 := addr_coeff (i := 8 * i) (o := 0) (j := 2 * i) fF (by omega) (by omega)
  have eF1 := addr_coeff (i := 8 * i) (o := 4) (j := 2 * i + 1) fF (by omega) (by omega)
  have eG0 := addr_coeff (i := 8 * i) (o := 0) (j := 2 * i) fG (by omega) (by omega)
  have eG1 := addr_coeff (i := 8 * i) (o := 4) (j := 2 * i + 1) fG (by omega) (by omega)
  have eH0 := addr_coeff (i := 8 * i) (o := 0) (j := 2 * i) fH (by omega) (by omega)
  have eH1 := addr_coeff (i := 8 * i) (o := 4) (j := 2 * i + 1) fH (by omega) (by omega)
  have eS := addr_ptr (ps s₀) (4 * i) 0 (by omega)
  have cF0 := coeff_contains (F s₀) (i := 2 * i) (by rw [n_eq]; omega)
  have cF1 := coeff_contains (F s₀) (i := 2 * i + 1) (by rw [n_eq]; omega)
  have cG0 := coeff_contains (G s₀) (i := 2 * i) (by rw [n_eq]; omega)
  have cG1 := coeff_contains (G s₀) (i := 2 * i + 1) (by rw [n_eq]; omega)
  have cH0 := coeff_contains (H s₀) (i := 2 * i) (by rw [n_eq]; omega)
  have cH1 := coeff_contains (H s₀) (i := 2 * i + 1) (by rw [n_eq]; omega)
  have cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * i + 0)) 4 :=
    contains_off (by omega) (by omega)
  have iR : ∀ {R : Region} {a : Addr} {n : Nat}, R ∈ s₀.rd ++ s₀.wr → R.Contains a n →
      InRegions (s.rd ++ s.wr) a n := fun hR hc => by rw [h.rd, h.wr]; exact inRegions_of hR hc
  have iW : ∀ {R : Region} {a : Addr} {n : Nat}, R ∈ s₀.wr → R.Contains a n → InRegions s.wr a n :=
    fun hR hc => by rw [h.wr]; exact inRegions_of hR hc
  -- The values read.
  have vF : ∀ j < 256, coeffAt s.mem (F s₀) j = BitVec.ofNat 32 ((fp s₀)[j]!).val := fun j hj => by
    rw [frame_coeff h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hf.symm)
      (by rw [n_eq]; exact hj), hm.f j hj]
    exact ofNat_val_eq (polyAt_val hp.redF (by rw [n_eq]; exact hj)).symm
  have vG : ∀ j < 256, coeffAt s.mem (G s₀) j = BitVec.ofNat 32 ((gp s₀)[j]!).val := fun j hj => by
    rw [frame_coeff h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hg.symm)
      (by rw [n_eq]; exact hj), hm.g j hj]
    exact ofNat_val_eq (polyAt_val hp.redG (by rw [n_eq]; exact hj)).symm
  have vS : s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * i + 0)) 32 = BitVec.ofNat 32 (gamma i).val := by
    rw [h.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hs.symm)
      (by decide), Nat.add_zero, hm.tab i hi, gammaTable_eq, gammas_getD hi]
  refine WP.mono (body_ok h.r0 h.r1 h.r2 h.r3 h.r8 h.r11
    (by rw [eF0]; exact iR (by simp [hp.rd]) cF0) (by rw [eF1]; exact iR (by simp [hp.rd]) cF1)
    (by rw [eG0]; exact iR (by simp [hp.rd]) cG0) (by rw [eG1]; exact iR (by simp [hp.rd]) cG1)
    (by rw [eS]; exact iR (by simp [hp.wr]) cS) (by rw [eH0]; exact iW (by simp [hp.wr]) cH0)
    (by rw [eH1]; exact iW (by simp [hp.wr]) cH1))
    fun s' ⟨r0, r1, r2, r3, r8, r11, z, lr, rd, wr, sp, m⟩ => ⟨⟨?_, ?_, ?_, ?_, r8, ?_, lr.trans h.lr,
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 8 i
  · rw [r1]; exact ptr_succ _ 8 i
  · rw [r2]; exact ptr_succ _ 8 i
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r11]; exact count_sub (k := 1) hi
  · rw [m, eH0, eH1]
    exact (h.frame.writeW (List.mem_singleton_self _) _ cH0).writeW (List.mem_singleton_self _) _ cH1
  · rw [m, eF0, eF1, eG0, eG1, eH0, eH1, eS]
    show ∀ j < 256, coeffAt ((s.mem.writeW (coeffAddr (H s₀) (2 * i)) _).writeW _ _) _ j = _
    rw [← coeffAt_eq, ← coeffAt_eq, ← coeffAt_eq, ← coeffAt_eq, vF _ (by omega), vF _ (by omega),
      vG _ (by omega), vG _ (by omega), vS, even_eq, red_mac, ← out_even s₀ hi, ← out_odd s₀ hi,
      show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    exact coeff_one (a := 2 * i + 1) (by omega) (coeff_one (a := 2 * i) (by omega) h.coeff rfl) rfl
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-! ## Setup and the end -/

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r3 512 ++ table gammaTable .r3 ++ consts ++ ([.mov .r11 (.imm 128)] : List Instr)))
      s₀ fun s => Setup s₀ s.mem ∧ Inv s₀ s.mem 0 s := by
  have fS := hp.fitS
  have wS : ∀ {o n : Nat}, o + n ≤ 1024 → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) n := fun h => by
    rw [hp.wr]; exact inRegions_of (by simp) (contains_off h (by omega))
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r3 (off := 512) (by decide) (fit_le (by decide) fS) fun i hi => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact wS (by omega)) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  have g3 : (s₁.gpr .r3) = ps s₀ := by rw [h₁.gpr]
  refine WP.mono (table_ok gammaTable (by decide) (b := .r3) (by decide) (by rw [g3]; exact fit_le (by decide) fS)
    fun k hk => by rw [g3, h₁.wr]; exact wS (by omega)) fun s₂ h₂ => ?_
  -- The memory after the setup, and its bytes outside `scratch`.
  have hS : (S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have fr : Frame [polyRegion (S s₀)] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · rw [List.mem_singleton] at hr; subst hr
      exact region_sub_off (by decide)
    · rw [List.mem_singleton] at hr; subst hr
      rw [g3, ← add_ofNat_zero (State.addr (ps s₀))]
      exact region_sub_off (by decide)
  have hm : Setup s₀ s₂.mem := by
    refine ⟨fun i hi => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rw [h₂.frame.readW (r := ⟨S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact h₁.saved i hi
      · rw [List.mem_singleton] at hr; subst hr
        rw [g3, add_ofNat_add, ← add_ofNat_zero (State.addr (ps s₀))]
        exact region_disj_off (by omega) (by omega) (by omega) hS
    · have := h₂.tab j hj; rwa [g3] at this
    · exact frame_coeff fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.fs)
        (by rw [n_eq]; exact hj)
    · exact frame_coeff fr (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.gs)
        (by rw [n_eq]; exact hj)
  have e : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => (h₂.gpr r hr).trans (by rw [h₁.gpr])
  have e0 := e .r0 (by decide)
  have e1 := e .r1 (by decide)
  have e2 := e .r2 (by decide)
  have e3 := e .r3 (by decide)
  have elr := e .lr (by decide)
  run_block [consts, e0, e1, e2, e3, elr, h₂.rd, h₁.rd, h₂.wr, h₁.wr, h₂.sp, h₁.sp, consts_val, hm, true_and]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, Frame.refl _ _, fun j _ => ?_⟩ <;> simp [e0, e1, e2, e3, elr]

theorem restore_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {s : State}
    (h : Inv s₀ m₁ 128 s) :
    WP isa (.block (restoreRegs .r3 0)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ PolyIs s'.mem (H s₀) (multiplyNTTs (fp s₀) (gp s₀)) := by
  have fS := hp.fitS
  have hS : (S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have e3 : State.addr (s.gpr .r3) + BitVec.ofNat 64 0 = S s₀ + BitVec.ofNat 64 512 := by
    rw [h.r3, addr_add (by omega), add_ofNat_zero]
  refine WP.mono (restoreRegs_ok .r3 (by decide) (off := 0) (by decide) (by rw [h.r3]; bv_omega)
    (g := s₀.gpr) (by
      rw [e3]
      intro i hi
      rw [h.frame.readW (r := ⟨S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact hm.sav i hi
      · rw [List.mem_singleton] at hr; subst hr
        refine hp.hs.symm.sub_left ?_
        rw [add_ofNat_add]
        exact region_sub_off (by omega))
    fun i hi => by
      rw [e3, h.rd, h.wr, hp.wr, add_ofNat_add]
      exact inRegions_of (R := polyRegion (S s₀)) (by simp) (contains_off (by omega) (by omega)))
    fun s' h' => ⟨preserved_of_restore h' h.lr, h'.sp.trans h.sp, ?_⟩
  rw [h'.mem]
  exact polyIs_of_coeffAt fun j hj => by
    rw [h.coeff j (by rw [n_eq] at hj; exact hj), ite_eq_left (by rw [n_eq] at hj; omega)]; rfl

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa multiplyNTTs s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      PolyIs s.mem (H s₀) (Spec.MlKem.multiplyNTTs (fp s₀) (gp s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => WP.seq ?_)
  exact wp_loop_ne (Inv s₀ s₁.mem) (N := 128) (by decide) (fun i hi s h => step hp hm hi h)
    (fun s h => restore_ok hp hm h) h₁

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.mulContract Arm.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem.mulContract, Spec.MlKem.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x4000, 1024⟩]

theorem verified : Verified Arm.target Impl.MlKem.Arm.multiplyNTTs (Spec.MlKem.mulContract Arm.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.r0, .r1, .r2, .r3] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, hpres, hsp, h⟩ := correct hp
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlKem.mulContract, Spec.MlKem.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlKem.mulContract, Spec.MlKem.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨-, h0, h1, h2, h3⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.mulContract, Spec.MlKem.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.Arm.Mul
