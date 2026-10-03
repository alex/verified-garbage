import VerifiedGarbage.Proof.Scrypt.X86.BlockMix

/-!
# scryptBlockMix on x86 (32-bit): the whole function

The prologue saves our caller's `ebx`, `esi`, `edi` and `ebp` in `scratch` and
sets up the loop's registers from the arguments; the loop runs the `r` pairs;
the epilogue restores the registers.
-/

namespace VG.Proof.Scrypt.X86.BlockMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movm wp_add wp_subi)
open VG.Proof.Scrypt.Memory (add_ofNat InRegions.of_mem frame_bytesAt bytesAt_add
  bytesAt_blocks)

/-! ## The prologue -/

/-- The prologue's register moves. -/
def bmSetup : List Instr :=
  .mov .ebx (.mem (at_ .esp 4)) :: .mov .esi (.mem (at_ .esp 12)) ::
    (timesR 64 ++ ([.mov .edi (.reg .esi), .alu .add .edi (.reg .eax), .mov .ebp (.reg .ebx),
      .alu .add .ebp (.reg .eax), .alu .add .ebp (.reg .eax), .alu .sub .ebp (.imm 64)] : List Instr))

theorem prologue_eq : bmPrologue =
    .mov .eax (.mem (at_ .esp 20)) :: (bmSaved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++ bmSetup) :=
  rfl

theorem bmSaved_bound : ∀ p ∈ bmSaved, p.2 + 4 ≤ 128 ∧ 64 ≤ p.2 ∧ p.1 ≠ .eax := by decide

theorem bmSaved_fits : Spill.Fits 128 bmSaved := by decide

theorem bmSaved_addr (s₀ : State) (hp : Pre s₀) :
    ∀ p ∈ bmSaved, addr (sc s₀) p.2 = scA s₀ + BitVec.ofNat 64 p.2 :=
  Spill.addr_eq_of_fits hp.s_nw bmSaved_fits

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, (∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r) → s₁.gpr .eax = sc s₀ → s₁.rd = s₀.rd →
      s₁.wr = s₀.wr → Frame [scR s₀] s₀.mem s₁.mem → Saved s₀ s₁.mem → WP isa (.block rest) s₁ Q) :
    WP isa (.block (.mov .eax (.mem (at_ .esp 20)) ::
      (bmSaved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++ rest))) s₀ Q := by
  have hs := hp.s_nw
  refine wp_movm (a := addr (esp₀ s₀) 20) rfl (arg_in hp (by omega) (by omega)) fun s₁ u₁ => ?_
  have e : s₁.gpr .eax = sc s₀ := u₁.gpr
  have ha := bmSaved_addr s₀ hp
  refine Spill.save_ok bmSaved (fun p hp' => ?_) fun s₂ u₂ => ?_
  · rw [e, u₁.wr, hp.wr, ha p hp']
    exact InRegions.of_mem (by simp) (in_s s₀ (bmSaved_fits.1 p hp'))
  refine k s₂ (fun r hr => by rw [u₂.gpr, u₁.other r hr]) (by rw [u₂.gpr, e]) (by rw [u₂.rd, u₁.rd])
    (by rw [u₂.wr, u₁.wr]) ?_ ?_
  · rw [u₂.mem, e, u₁.mem]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp' => by
      rw [ha p hp']; exact in_s s₀ (bmSaved_fits.1 p hp')
  · rw [u₂.mem, e, u₁.mem]
    exact (Spill.saveMem_saved_addr _ _ bmSaved_fits hs).congr ha
      fun p hp' => u₁.other _ (bmSaved_bound p hp').2.2

/-- The registers the loop starts with. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : ∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hf : Frame [scR s₀] s₀.mem s₁.mem)
    (hsv : Saved s₀ s₁.mem) :
    WP isa (.block bmSetup) s₁ (Inv s₀ 0) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hesp : s₁.gpr .esp = esp₀ s₀ := g _ (by decide)
  have hf' : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s₁.mem := hf.mono (by simp)
  have rd₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [hrd, hwr]
  unfold bmSetup
  refine wp_movm (a := addr (esp₀ s₀) 4) (by rw [ea_at, hesp])
    (by rw [rd₁]; exact arg_in hp (by omega) (by omega)) fun a ua => ?_
  refine wp_movm (a := addr (esp₀ s₀) 12) (by rw [ea_at, ua.other _ (by decide), hesp])
    (by rw [ua.rd, ua.wr, rd₁]; exact arg_in hp (by omega) (by omega)) fun b ub => ?_
  have eb : b.gpr .esp = esp₀ s₀ := by rw [ub.other _ (by decide), ua.other _ (by decide), hesp]
  have mb : b.mem = s₁.mem := by rw [ub.mem, ua.mem]
  have bx : b.gpr .ebx = bP s₀ := by
    rw [ub.other _ (by decide), ua.gpr, arg_keep hp hf' (by omega) (by omega)]; rfl
  have bs : b.gpr .esi = yP s₀ := by
    rw [ub.gpr, ua.mem, arg_keep hp hf' (by omega) (by omega)]; rfl
  refine timesR_ok (r := arg s₀ 1) (by rw [eb, mb, arg_keep hp hf' (by omega) (by omega)]; rfl)
    (by rw [eb, ub.rd, ub.wr, ua.rd, ua.wr, rd₁]; exact arg_in hp (by omega) (by omega))
    fun t e o mt rdt wrt => ?_
  refine wp_mov fun c uc => wp_add fun d ud => wp_mov fun f uf => wp_add fun i ui => wp_add fun j uj =>
    wp_subi fun l ul _ => WP.block_nil ?_
  have e64 : t.gpr .eax = BitVec.ofNat 32 (rr s₀ * 64) := by rw [e]; rfl
  have kl : ∀ r, r ≠ .ebp → r ≠ .edi → r ≠ .eax → r ≠ .ecx → r ≠ .edx → l.gpr r = b.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [ul.other _ h1, uj.other _ h1, ui.other _ h1, uf.other _ h1, ud.other _ h2, uc.other _ h2,
        o r h3 h4 h5]
  have ml : l.mem = s₁.mem := by rw [ul.mem, uj.mem, ui.mem, uf.mem, ud.mem, uc.mem, mt, mb]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega), ?_⟩
  · rw [ul.rd, uj.rd, ui.rd, uf.rd, ud.rd, uc.rd, rdt, ub.rd, ua.rd, hrd]
  · rw [ul.wr, uj.wr, ui.wr, uf.wr, ud.wr, uc.wr, wrt, ub.wr, ua.wr, hwr]
  · rw [kl _ (by decide) (by decide) (by decide) (by decide) (by decide), eb]
  · rw [kl _ (by decide) (by decide) (by decide) (by decide) (by decide), bx]; simp
  · rw [kl _ (by decide) (by decide) (by decide) (by decide) (by decide), bs]; simp
  · rw [ul.other _ (by decide), uj.other _ (by decide), ui.other _ (by decide), uf.other _ (by decide),
      ud.gpr, uc.gpr, uc.other _ (by decide), e64, o _ (by decide) (by decide) (by decide), bs]
    congr 2; omega
  · rw [ul.gpr, uj.gpr, ui.gpr, ui.other .eax (by decide), uf.gpr, uf.other .eax (by decide),
      ud.other .ebx (by decide), ud.other .eax (by decide), uc.other .ebx (by decide),
      uc.other .eax (by decide), e64, o _ (by decide) (by decide) (by decide), bx, add32,
      sub32 _ (by omega)]
    show _ = bP s₀ + BitVec.ofNat 32 (128 * rr s₀ - 64)
    congr 2; omega
  · rw [ml]; exact hf'
  · rw [ml]; exact hsv
  · rw [ml]
    show bytesAt s₁.mem (bA s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega]
    exact b_frame hp hf' (by omega)

/-! ## The loop -/

theorem loop_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop (bmBody c) .ne) s (Inv s₀ (rr s₀)) :=
  count_loop hp.pos (Inv s₀) (fun _ hk _ h => body_ok hS hp hk h) h

/-! ## The epilogue -/

theorem epilogue_eq : bmEpilogue =
    .mov .eax (.mem (at_ .esp 20)) :: (bmSaved.map (fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) ++ []) :=
  rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧ (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  have hs := hp.s_nw
  rw [epilogue_eq]
  refine wp_movm (a := addr (esp₀ s₀) 20) (by rw [ea_at, h.esp])
    (by rw [h.rd, h.wr]; exact arg_in hp (by omega) (by omega)) fun s₁ u₁ => ?_
  have e : s₁.gpr .eax = sc s₀ := by rw [u₁.gpr, arg_keep hp h.frame (by omega) (by omega)]; rfl
  have ha := bmSaved_addr s₀ hp
  refine Spill.restore_ok bmSaved (by decide) (fun p hp' => ?_)
    (by rw [e, u₁.mem]; exact h.saved.congr (fun p hp' => (ha p hp').symm) fun _ _ => rfl)
    fun s₂ u => WP.block_nil ⟨by rw [u.mem, u₁.mem],
      u.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp])⟩
  rw [e, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr, ha p hp']
  exact InRegions.of_mem (by simp) (in_s s₀ (bmSaved_fits.1 p hp'))

/-! ## The whole function -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yA s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  rw [blockMix_eq, show 128 * rr s₀ = 64 * rr s₀ + 64 * rr s₀ by omega, bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

theorem correct {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (blockMixWith c) s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Scrypt.blockMixX86.post s₀ s' := by
  unfold blockMixWith
  refine WP.seq ?_
  rw [prologue_eq]
  refine save_ok hp fun s₁ g _ hrd hwr hf hsv => ?_
  refine WP.mono (setup_ok hp g hrd hwr hf hsv) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hg'⟩ => ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₃.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.ret_y, hp.ret_s, ret_stk hp]
  · show bytesAt s'.mem (yA s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀)
    rw [hm']
    exact post_of fun i hi => h₃.done i hi

end VG.Proof.Scrypt.X86.BlockMix
