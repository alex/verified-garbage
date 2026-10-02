import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateLoop

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_update` is correct
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem ofNat_ne_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x != 0) = !decide (x = 0) := by
  have : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
      simpa using this
    · intro he; rw [he]; rfl
  rw [bne, this]

theorem eval_x23 {s : State} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr .x23 = BitVec.ofNat 64 x) :
    isa.eval (.nonzero .x .x23) s = some !decide (x = 0) := by
  show some (s.read .x .x23 != 0) = _
  rw [State.read, h, BitVec.setWidth_eq, ofNat_ne_zero hx]

theorem eval_zero_x23 {s : State} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr .x23 = BitVec.ofNat 64 x) :
    isa.eval (.zero .x .x23) s = some (decide (x = 0)) := by
  show some (s.read .x .x23 == 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  have := ofNat_ne_zero hx
  rw [bne] at this
  cases hb : (BitVec.ofNat 64 x == 0) <;> rw [hb] at this <;> cases hd : decide (x = 0) <;> simp_all

theorem loop_ok (v : Ctr32Impl) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv s₀ k s) : WP isa (.loop (body v.callee) (.nonzero .x .x23)) s (LInv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body v.callee) (c := .nonzero .x .x23) (Q := LInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok v hp hk h) fun s' h' => ?_
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have ev := eval_x23 (x := N s₀ - (k + 1)) (by omega) h'.x23
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## Saving and restoring the registers -/

theorem readW_writeW_other (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hd he) (by decide)

/-- Each slot holds the register saved there. -/
theorem savedMem_slot (s : State) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (savedMem s).readW (s.gpr .x5 + BitVec.ofNat 64 d) 64 = s.gpr r := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  simp only [savedMem, saved, List.foldl]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)])

theorem restore_ok (s : State) {B : Addr} (hb : s.gpr .x24 = B)
    (hr : ∀ d, 2064 ≤ d → d + 8 ≤ 2120 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa restore s = some s' ∧
      (∀ r d, (r, d) ∈ saved → s'.gpr r = s.mem.readW (B + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x30 → r ≠ .x24 →
        s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp (config := {decide := true}) only [restore, saved, List.map, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write,
      wr_write, ite_true, ite_false, Option.bind_some, Option.map_some, hb,
      hr 2064 (by decide) (by decide), hr 2072 (by decide) (by decide), hr 2080 (by decide) (by decide),
      hr 2088 (by decide) (by decide), hr 2096 (by decide) (by decide), hr 2104 (by decide) (by decide),
      hr 2112 (by decide) (by decide)]
    rfl, ?_⟩
  refine ⟨fun r d h => ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ => ?_, rfl, rfl⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [gpr_write, Mem.readW]
  · simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆, h₇]

/-! ## The whole function -/

theorem x4_ofNat (s₀ : State) : s₀.gpr .x4 = BitVec.ofNat 64 (N s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [N]

theorem slots_disj {s₀ : State} (hp : UPre s₀) :
    ∀ r ∈ [stR s₀, ⟨S s₀, 2064⟩], (⟨S s₀ + BitVec.ofNat 64 2064, 56⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [stR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d) (h₂ : d + 8 ≤ 2120) :
    m.readW (S s₀ + BitVec.ofNat 64 d) 64 = (savedMem s₀).readW (S s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 2064, 56⟩) (slot_contains _ h₁ h₂) (slots_disj hp) (by decide)

theorem prologue_wp {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s₁ => LInv s₀ 0 s₁ := by
  obtain ⟨s₁, run₁, x19₁, x20₁, x21₁, x22₁, x23₁, x24₁, keep₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    prologue_ok s₀ fun d _ h₂ => by
      rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have stSaved : Spec.Aes.bytesAt (savedMem s₀) (St s₀) 16 = Spec.Aes.bytesAt s₀.mem (St s₀) 16 :=
    Proof.Cmac.bytesAt_frame16 (savedMem_frame s₀) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (UPre.scr_sub (by decide))
  exact { x19 := x19₁, x20 := x20₁, x21 := x21₁
          x22 := by rw [x22₁]; simp
          x23 := by rw [x23₁, x4_ofNat]; rfl
          x24 := x24₁
          other := fun r _ h19 h20 h21 h22 h23 h24 _ => keep₁ r h19 h20 h21 h22 h23 h24
          sp := sp₁, rd := rd₁, wr := wr₁
          frame := by rw [mem₁]; exact Frame.refl _ _
          state := by rw [mem₁, stSaved]; rfl }

theorem mid_wp (v : Ctr32Impl) {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : LInv s₀ 0 s₁) :
    WP isa (.ite (.zero .x .x23) (.block []) (.loop (body v.callee) (.nonzero .x .x23))) s₁
      (LInv s₀ (N s₀)) := by
  have hN := (s₀.gpr .x4).isLt
  have ev := eval_zero_x23 (x := N s₀) hN (by rw [h.x23]; rfl)
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok v hp (by omega) h

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => GprAbi s₀ s' ∧ updateAArch64.post s₀ s' := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  obtain ⟨s₃, run₃, slot₃, keep₃, sp₃, mem₃⟩ :=
    restore_ok s₂ h₂.x24 fun d _ h₂' => by
      rw [rdwr, hp.rd, hp.wr]
      exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by have := hp.scr_wrap; omega))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have sl {r : Reg} {d : Nat} (h : (r, d) ∈ saved) : s₃.gpr r = s₀.gpr r := by
    have hd : 2064 ≤ d ∧ d + 8 ≤ 2120 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      omega
    rw [slot₃ r d h, slot_read hp h₂.frame hd.1 hd.2, savedMem_slot s₀ h]
  refine ⟨⟨fun r hr => ?_, by rw [sp₃, h₂.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sl (d := 2064) (by simp [saved])
    · exact sl (d := 2072) (by simp [saved])
    · exact sl (d := 2080) (by simp [saved])
    · exact sl (d := 2088) (by simp [saved])
    · exact sl (d := 2096) (by simp [saved])
    · exact sl (d := 2112) (by simp [saved])
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · exact sl (d := 2104) (by simp [saved])
  · show Spec.Aes.bytesAt s₃.mem (St s₀) 16 = Spec.Cmac.chain (ciph s₀) _ (blks s₀)
    rw [mem₃, h₂.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem update_wp (v : Ctr32Impl) {s₀ : State} (h0 : updateAArch64.pre s₀) :
    WP isa (update v.callee) s₀ fun s' => GprAbi s₀ s' ∧ updateAArch64.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ h₁ =>
    WP.seq (WP.mono (mid_wp v hp h₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.CmacAes.AArch64
