import VerifiedGarbage.Proof.CmacAes.Arm.UpdateLoop

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_update` is correct
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd wp_ldr eval_eq)

/-! ## Restoring the registers -/

/-- Loads of the registers `l` from `b + offset`, none of them `b`. -/
theorem restoreB_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ b ∧ p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 b p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h2, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldr h1 (addr_add h2) h3 fun s₁ u₁ => ?_
    have eb : s₁.gpr b = s.gpr b := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr hsp => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp)
    · rw [eb, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

theorem restore_eq : restore = (saved.take 7).map (fun p => Instr.ldr p.1 .r10 p.2) ++
    ([.ldr .r10 .r10 2088] : List Instr) := rfl

theorem take7_ne : ∀ p ∈ saved.take 7, p.1 ≠ .r10 := by decide

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [stR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d)
    (h₂ : d + 4 ≤ 2096) :
    m.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = (savedMem s₀).readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by omega))
    · exact Offset.disjoint_base _ h₁ (by omega)
    · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega))) (by decide)

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv s₀ (N s₀) s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ updateArm.post s₀ s' := by
  have hsc := hp.scr_fit
  have rdwr : s.rd ++ s.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inS : ∀ d, d + 4 ≤ 2176 → InRegions (s.rd ++ s.wr) (State.addr (S s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact ⟨scrR s₀, by simp, Offset.contains_base _ hd (by omega)⟩
  have sl : ∀ r d, (r, d) ∈ saved → s.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      have hb := saved_bound _ hrd
      rw [slot_read hp h.frame hb.1 hb.2, savedMem_slot s₀ hrd]
  rw [restore_eq]
  refine restoreB_ok (saved.take 7) s _ (by decide) (fun p hp' => ?_) fun s₁ ld₁ ho₁ m₁ rd₁ wr₁ sp₁ => ?_
  · have hb := saved_bound p (List.mem_of_mem_take hp')
    exact ⟨take7_ne p hp', by omega, by rw [h.r10]; omega, by rw [h.r10]; exact inS _ (by omega)⟩
  refine wp_ldr (a := State.addr (S s₀) + BitVec.ofNat 64 2088) (by decide)
    (by rw [ho₁ _ (by decide), h.r10]; exact hp.scrA (by decide))
    (by rw [rd₁, wr₁]; exact inS _ (by decide)) fun s₂ u₂ => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have ld : ∀ r d, (r, d) ∈ saved.take 7 → s₂.gpr r = s₀.gpr r := fun r d hrd => by
      have hne : r ≠ .r10 := take7_ne _ hrd
      rw [u₂.other _ hne, ld₁ _ hrd, h.r10, sl r d (List.mem_of_mem_take hrd)]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ld _ 2064 (by decide)
    · exact ld _ 2068 (by decide)
    · exact ld _ 2072 (by decide)
    · exact ld _ 2076 (by decide)
    · exact ld _ 2080 (by decide)
    · exact ld _ 2084 (by decide)
    · rw [u₂.gpr, m₁, sl .r10 2088 (by decide)]
    · rw [u₂.other _ (by decide), ho₁ _ (by decide), h.r11]
    · exact ld _ 2092 (by decide)
  · rw [u₂.sp, sp₁, h.sp]
  · show Spec.Aes.bytesAt s₂.mem (State.addr (St s₀)) 16 = Spec.Cmac.chain (ciph s₀) _ (blks s₀)
    rw [u₂.mem, m₁, h.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

/-! ## The whole function -/

theorem mid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : LInv s₀ 0 s₁) (hz : s₁.z = decide (N s₀ = 0)) :
    WP isa (.ite .eq (.block []) (.loop body .ne)) s₁ (LInv s₀ (N s₀)) := by
  have ev : isa.eval .eq s₁ = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp (by omega) h

theorem update_wp {s₀ : State} (h0 : updateArm.pre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ updateArm.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (mid_wp hp h₁ hz) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.CmacAes.Arm
