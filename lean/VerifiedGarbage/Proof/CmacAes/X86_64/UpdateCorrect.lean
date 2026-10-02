import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateLoop

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_update` is correct
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
    simpa using this
  · intro he; rw [he]; rfl

theorem loop_ok (v : Ctr32Impl) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv s₀ k s) : WP isa (.loop (body v.callee) .ne) s (LInv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body v.callee) (c := .ne) (Q := LInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok v hp hk h) fun s' ⟨h', zf'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by simp [eval, zf', hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by simp [eval, zf', hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## Saving and restoring the registers -/

theorem readW_writeW_other (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hd he) (by decide)

/-! ## The whole function -/

theorem r8_ofNat (s₀ : State) : s₀.gpr .r8 = BitVec.ofNat 64 (N s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [N]

theorem slots_disj {s₀ : State} (hp : UPre s₀) :
    ∀ r ∈ [stR s₀, ⟨S s₀, 2064⟩, stkR s₀], (⟨S s₀ + BitVec.ofNat 64 2064, 48⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)
  · exact hp.stk_scr.symm.sub_left (UPre.scr_sub (by decide))

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [stR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d) (h₂ : d + 8 ≤ 2112) :
    m.readW (S s₀ + BitVec.ofNat 64 d) 64 = (savedMem s₀).readW (S s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 2064, 48⟩) (slot_contains _ h₁ h₂) (slots_disj hp) (by decide)

theorem prologue_wp {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s₁ => LInv s₀ 0 s₁ ∧ s₁.zf = some (decide (N s₀ = 0)) := by
  have hN := (s₀.gpr .r8).isLt
  obtain ⟨s₁, run₁, rbx₁, rbp₁, r12₁, r13₁, r14₁, r15₁, rsp₁, zf₁, mem₁, rd₁, wr₁⟩ :=
    prologue_ok s₀ fun d _ h₂ => by
      rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  refine WP.of_runBlock ⟨s₁, run₁, ?_, ?_⟩
  · have stSaved : Spec.Aes.bytesAt (savedMem s₀) (St s₀) 16 = Spec.Aes.bytesAt s₀.mem (St s₀) 16 :=
      bytesAt_frame' (savedMem_frame s₀) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (UPre.scr_sub (by decide))
    exact { rbx := rbx₁, rbp := rbp₁, r12 := r12₁
            r13 := by rw [r13₁]; simp
            r14 := by rw [r14₁, r8_ofNat]; rfl
            r15 := r15₁, rsp := rsp₁, rd := rd₁, wr := wr₁
            frame := by rw [mem₁]; exact Frame.refl _ _
            state := by rw [mem₁, stSaved]; rfl }
  · rw [zf₁, r8_ofNat, beq_zero hN]

theorem mid_wp (v : Ctr32Impl) {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : LInv s₀ 0 s₁)
    (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop (body v.callee) .ne)) s₁ (LInv s₀ (N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := hz
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok v hp (by omega) h

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => gprPreserved s₀ s' ∧ updateX86_64.post s₀ s' := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  have hsv : Spill.Saved s₂.mem (s₂.gpr .r15) s₀.gpr saved := fun p hp' => by
    have := saved_bound p hp'
    rw [h₂.r15, slot_read hp h₂.frame this.1 this.2]
    exact Spill.saveMem_saved _ _ _ _ (by decide) p hp'
  refine WP.mono (Spill.restore_ok .r15 saved s₀.gpr s₂ (by decide) (fun p hp' => ?_) hsv)
    fun s₃ ⟨g₁, g₂, mem₃, _⟩ => ⟨⟨Spill.calleeSaved_ok g₁ g₂ (by decide) h₂.rsp, ?_⟩, ?_⟩
  · have := saved_bound p hp'
    rw [rdwr, hp.rd, hp.wr, h₂.r15]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by have := hp.scr_wrap; omega))
  · rw [mem₃]
    refine (UPre.big_of h₂.frame).readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · show Spec.Aes.bytesAt s₃.mem (St s₀) 16 = Spec.Cmac.chain (ciph s₀) _ (blks s₀)
    rw [mem₃, h₂.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem update_wp (v : Ctr32Impl) {s₀ : State} (h0 : updateX86_64.pre s₀) :
    WP isa (update v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ updateX86_64.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (mid_wp v hp h₁ z₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.CmacAes.X86_64
