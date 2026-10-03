import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.Mont

/-!
# Multiword arithmetic on x86-64: the BMI2/ADX multiplication in constant time

As for `montMul_ct`, the pieces that load from the header are checked by the
taint analysis from `rdi`, and what follows them from the registers they set,
which `Two` fixes. The size test, the rows' loop and the end of each row
compare with values from the header, so the branch and the loop are taken
alike in both runs because `Lay` fixes `w` (`two_ite`, `two_loop`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.MlKem.X86_64

/-- Before row `i` of `b`'s multiplication: the window and the bases. -/
def FW (b : Nat) (L : Lay) (i : Nat) (t : State) : Prop :=
  GoodL L t ∧ SizeOk L.w ∧ t.gpr .r8 = off L.B (slot L.w aAcc + 16 + 8 * i) ∧
  t.gpr .r9 = off L.B (slot L.w b) ∧ t.gpr .r10 = off L.B (slot L.w aN) ∧ t.gpr .rbx = BitVec.ofNat 64 L.w

theorem FW.pins {b : Nat} {L : Lay} {i : Nat} {s₁ s₂ : State} (h₁ : FW b L i s₁) (h₂ : FW b L i s₂) :
    ∀ r ∈ [Reg.rdi, .r8, .r9, .r10, .rbx], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.1.1.rdi, h₂.1.1.rdi]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2]

/-- After `rowBase`: `rax` too. -/
def FR (a b : Nat) (p : Lay × Nat) (t : State) : Prop :=
  FW b p.1 p.2 t ∧ t.gpr .rax = off p.1.B (slot p.1.w a) - off p.1.B (slot p.1.w aAcc + 16)

theorem pins_fr (a b : Nat) : Pins (FR a b) [.rdi, .r8, .r9, .r10, .rbx, .rax] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · subst h; rw [h₁.2, h₂.2]

/-- After `finishBases`: the registers of `subMod` and `selectAcc`. -/
def FF (o : Nat) (L : Lay) (t : State) : Prop :=
  t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .r8 = off L.B (slot L.w aTmp) ∧ t.gpr .rsi = off L.B (slot L.w aAcc) ∧
  t.gpr .rbx = off L.B (slot L.w o) ∧ t.gpr .r10 = off L.B (slot L.w aN)

theorem pins_ff (o : Nat) : Pins (FF o) [.r12, .r8, .rsi, .rbx, .r10] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]

theorem SizeOk.lt {w : Nat} (h : SizeOk w) : w < 2 ^ 31 := by unfold SizeOk at h; omega

/-- A row keeps the bases and the header, and moves the window. -/
theorem row_fw {a b : Nat} (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc)
    (hb2 : b ≠ aTmp) (L : Lay) (j : Nat) (s : State) (hj : j < L.w) (h : FW b L j s) :
    WP isa (row a) s fun s' => isa.eval .ne s' = some (decide (j + 1 < L.w)) ∧
      (j + 1 < L.w → FW b L (j + 1) s') ∧ (j + 1 = L.w → FW b L L.w s') := by
  obtain ⟨⟨hg, hZ⟩, hsz, h8, h9, h10, hbx⟩ := h
  have hn := hg.scr.nowrap
  have hg0 : hdrBytes ≤ slot L.w aAcc := by unfold slot; omega
  refine WP.mono (row_ok hg.scr hg.rdi hg.hdr hZ ha hb ha1 ha2 hb1 hb2 rfl hj hsz.1 hsz.2.1
    (by have := hsz.lt; omega) h8 h9 h10 hbx) fun s' ⟨_, ho, h8', hz, k⟩ => ?_
  have hg' : GoodL L s' := ⟨⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ho (by omega)⟩, hZ⟩
  have hfw : FW b L (j + 1) s' := ⟨hg', hsz, by rw [h8', show slot L.w aAcc + 16 + 8 * j + 8 = slot L.w aAcc + 16 + 8 * (j + 1) by omega], (k.gpr (by decide)).trans h9,
    (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans hbx⟩
  refine ⟨?_, fun _ => hfw, fun he => he ▸ hfw⟩
  simp only [eval, hz, Option.map_some]
  congr 1
  by_cases he : j + 1 = L.w
  · simp [he]
  · simp [he]; omega

/-- The fused multiplication is constant time, given that the taint analysis
checks its header loads from `rdi`. -/
theorem fused_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) hc₁).isSome = true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) hc₂).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) hc₃).isSome = true) :
    RelCT isa (Two fun L s => GoodL L s ∧ SizeOk L.w) (fused o a b) fun _ _ => True := by
  unfold fused
  -- The bases.
  refine RelCT.seq (two_piece (Ψ := fun L s => FW b L 0 s) [.rdi]
    (fun L s₁ s₂ h₁ h₂ => pins_good L s₁ s₂ h₁.1 h₂.1) hS fun L s ⟨⟨hg, hZ⟩, hsz⟩ =>
      WP.mono (adxSetup_ok hg.scr hg.rdi hg.hdr hZ hb) fun t ⟨h9, h10, h8, hbx, hm, k⟩ =>
        ⟨⟨⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hsz, h8, h9, h10, hbx⟩) ?_
  -- The windows := 0.
  refine RelCT.seq (two_piece (Ψ := fun L s => 0 < L.w ∧ FW b L 0 s) [.rdi, .r8, .r9, .r10, .rbx]
    (fun L s₁ s₂ h₁ h₂ => h₁.pins h₂) (by taint_decide) fun L s h => ?_) ?_
  · obtain ⟨⟨hg, hZ⟩, hsz, h8, h9, h10, hbx⟩ := h
    have hn := hg.scr.nowrap
    refine WP.mono (zeroWin_ok (A := slot L.w aAcc + 16) hg.scr (by rw [h8, Nat.mul_zero, Nat.add_zero]) hbx (by have := hsz.lt; omega)
      (by unfold slot aAcc at *; omega)) fun t ⟨_, ho', k⟩ => ⟨by have := hsz.2.1; omega, ⟨⟨hg.scr.congr k.2.2,
        (k.gpr (by decide)).trans hg.rdi, hg.hdr.of_outside ho' (by unfold slot hdrBytes; omega)⟩, hZ⟩, hsz,
      (k.gpr (by decide)).trans h8, (k.gpr (by decide)).trans h9, (k.gpr (by decide)).trans h10,
      (k.gpr (by decide)).trans hbx⟩
  -- The rows.
  refine RelCT.seq (two_loop (fun L => L.w) (Φ := fun L j s => FW b L j s) (Ψ := fun L s => FW b L L.w s) ?_
    (row_fw ha hb ha1 ha2 hb1 hb2)) ?_
  · unfold row
    refine RelCT.seq (two_piece (Ψ := FR a b) [.rdi] (fun p s₁ s₂ h₁ h₂ => pins_good p.1 s₁ s₂ h₁.2.1 h₂.2.1)
      hR fun p s ⟨_, h⟩ => ?_) (two_taint _ (pins_fr a b) (by taint_decide))
    obtain ⟨⟨hg, hZ⟩, hsz, h8, h9, h10, hbx⟩ := h
    exact WP.mono (rowBase_ok hg.scr hg.rdi hg.hdr hZ ha) fun t ⟨hax, hm, k⟩ =>
      ⟨⟨⟨⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hsz,
        (k.gpr (by decide)).trans h8, (k.gpr (by decide)).trans h9, (k.gpr (by decide)).trans h10,
        (k.gpr (by decide)).trans hbx⟩, hax⟩
  -- `T - m`, and the selection.
  unfold finish
  refine RelCT.seq (two_piece (Ψ := FF o) [.rdi] (fun L s₁ s₂ h₁ h₂ => pins_good L s₁ s₂ h₁.1 h₂.1) hF
    fun L s h => ?_) (two_taint _ (pins_ff o) (by taint_decide))
  obtain ⟨⟨hg, hZ⟩, hsz, h8, h9, h10, hbx⟩ := h
  exact WP.mono (finishBases_ok hg.scr hg.rdi hg.hdr hZ ho) fun t ⟨h12, h8', hsi, hbx', _, k⟩ =>
    ⟨h12, h8', hsi, hbx', (k.gpr (by decide)).trans h10⟩

/-- `montMulAdx` is constant time, given that the taint analysis checks its
header loads from `rdi` (and `montMul`'s). -/
theorem montMulAdx_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    {hc₀ hc₁ hc₂ hc₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) hc₀).isSome = true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) hc₁).isSome = true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) hc₂).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) hc₃).isSome = true) :
    RelCT isa (Two GoodL) (montMulAdx o a b) fun _ _ => True := by
  unfold montMulAdx
  refine RelCT.seq (two_piece (Ψ := fun L s => GoodL L s ∧ s.zf = some (decide (SizeOk L.w))) [.rdi] pins_good
    (by taint_decide) fun L s ⟨hg, hZ⟩ => WP.mono (sizeTest_ok hg.scr hg.rdi hg.hdr hZ) fun t ⟨hz, hm, k⟩ =>
      ⟨⟨⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hz⟩) ?_
  refine two_ite (fun L s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨hg, hz⟩, he⟩ => ⟨hg, ?_⟩) (fused_ct ho ha hb ha1 ha2 hb1 hb2 hS hR hF)
    simp only [eval, hz, Option.some.injEq, decide_eq_true_eq] at he
    exact he
  · exact two_map id (fun L s h => h.1.1) (montMul_ct (by decide) (by decide) (by decide) ho ha hb hM)

/-- Montgomery multiplication with BMI2 and ADX (`montMulAdx`), for RSA. -/
def Mont.adx : Mont where
  mm := montMulAdx
  ok hg hZ hw hw' _ _ _ ho ha hb d1 d2 d3 d4 d5 d6 hinv hB :=
    WP.mono (montMulAdx_ok hg.scr hg.rdi hg.hdr hZ hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hinv hB)
      fun t' ⟨h1, h2, h3, k⟩ => ⟨⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, h3.hdr hg.hdr⟩,
        h1, h2, h3, k⟩
  ct := by
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ <;>
    exact montMulAdx_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)

end VG.Proof.Bignum.X86_64
