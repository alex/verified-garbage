import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Scrypt.X86_64.BlockMix

/-!
# scryptBlockMix on x86-64: the whole function

Untrusted: everything here is checked by Lean. The prologue saves our
caller's registers in `scratch` and sets up the loop's; the loop runs the
`r` pairs; the epilogue restores the registers.
-/

namespace VG.Proof.Scrypt.X86_64.BlockMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.MdStream.X86_64 (Upd wp_mov wp_movm wp_store wp_add wp_subi)

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (sc s₀ + BitVec.ofNat 64 64) (s₀.gpr .rbx)).writeW
    (sc s₀ + BitVec.ofNat 64 72) (s₀.gpr .rbp)).writeW (sc s₀ + BitVec.ofNat 64 80)
    (s₀.gpr .r12)).writeW (sc s₀ + BitVec.ofNat 64 88) (s₀.gpr .r14)).writeW
    (sc s₀ + BitVec.ofNat 64 96) (s₀.gpr .r15)).writeW (sc s₀ + BitVec.ofNat 64 104)
    (s₀.gpr .r13)

theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 =
      m.readW (p + BitVec.ofNat 64 d) 64 := by
  refine Mem.readW_writeW_sep (fun x hx hy => ?_) (by decide)
  have t₁ : (BitVec.ofNat 64 d).toNat = d := toNat_ofNat_lt (by omega)
  have t₂ : (BitVec.ofNat 64 e).toNat = e := toNat_ofNat_lt (by omega)
  bv_omega

set_option simprocs false in
theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  intro p hp
  simp only [bmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [saveMem, Mem.readW_writeW_self64, readW_writeW_off]

theorem saveMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 128 → (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => in_s s₀ hd
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 64 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 72 (by omega))).writeW (List.mem_singleton_self _) _
    (c 80 (by omega))).writeW (List.mem_singleton_self _) _ (c 88 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 96 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 104 (by omega))

theorem prologue_eq : bmPrologue =
    ([.store (at_ .r8 64) .rbx, .store (at_ .r8 72) .rbp, .store (at_ .r8 80) .r12,
     .store (at_ .r8 88) .r14, .store (at_ .r8 96) .r15, .store (at_ .r8 104) .r13] : List Instr) ++
    ([.mov .r14 (.reg .rsi), .mov .rbx (.reg .rdi), .mov .rbp (.reg .rdx), .mov .r13 (.reg .r8),
     .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi),
     .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi),
     .mov .r12 (.reg .rdx), .alu .add .r12 (.reg .rsi),
     .mov .r15 (.reg .rdi), .alu .add .r15 (.reg .rsi), .alu .add .r15 (.reg .rsi),
     .alu .sub .r15 (.imm 64)] : List Instr) := rfl

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.mem = saveMem s₀ →
      WP isa (.block rest) s₁ Q) :
    WP isa (.block (([.store (at_ .r8 64) .rbx, .store (at_ .r8 72) .rbp, .store (at_ .r8 80) .r12,
      .store (at_ .r8 88) .r14, .store (at_ .r8 96) .r15, .store (at_ .r8 104) .r13] : List Instr) ++ rest))
      s₀ Q := by
  have o : ∀ d, d + 8 ≤ 128 → ∀ s : State, s.wr = s₀.wr →
      InRegions s.wr (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd s hw => by
    rw [hw, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ hd)
  simp only [List.cons_append, List.nil_append]
  refine wp_store (ea_at _ _ _) (o 64 (by omega) _ rfl) fun s1 g1 m1 r1 w1 => ?_
  refine wp_store (by rw [ea_at, g1]) (o 72 (by omega) _ w1) fun s2 g2 m2 r2 w2 => ?_
  refine wp_store (by rw [ea_at, g2, g1]) (o 80 (by omega) _ (w2.trans w1))
    fun s3 g3 m3 r3 w3 => ?_
  refine wp_store (by rw [ea_at, g3, g2, g1]) (o 88 (by omega) _ (w3.trans (w2.trans w1)))
    fun s4 g4 m4 r4 w4 => ?_
  refine wp_store (by rw [ea_at, g4, g3, g2, g1])
    (o 96 (by omega) _ (w4.trans (w3.trans (w2.trans w1)))) fun s5 g5 m5 r5 w5 => ?_
  refine wp_store (by rw [ea_at, g5, g4, g3, g2, g1])
    (o 104 (by omega) _ (w5.trans (w4.trans (w3.trans (w2.trans w1))))) fun s6 g6 m6 r6 w6 => ?_
  exact k s6 (by rw [g6, g5, g4, g3, g2, g1]) (by rw [r6, r5, r4, r3, r2, r1])
    (w6.trans (w5.trans (w4.trans (w3.trans (w2.trans w1)))))
    (by rw [m6, m5, m4, m3, m2, m1, g5, g4, g3, g2, g1]; rfl)

theorem dbl {a : Addr} {n : Nat} (h : a = BitVec.ofNat 64 n) : a + a = BitVec.ofNat 64 (2 * n) := by
  rw [h, ← BitVec.ofNat_add, Nat.two_mul]

set_option linter.unusedSimpArgs false in
/-- The registers the loop starts with. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [.mov .r14 (.reg .rsi), .mov .rbx (.reg .rdi), .mov .rbp (.reg .rdx),
     .mov .r13 (.reg .r8),
     .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi),
     .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi),
     .mov .r12 (.reg .rdx), .alu .add .r12 (.reg .rsi),
     .mov .r15 (.reg .rdi), .alu .add .r15 (.reg .rsi), .alu .add .r15 (.reg .rsi),
     .alu .sub .r15 (.imm 64)]) s₁ (Inv s₀ 0) := by
  have lt := r_lt hp
  have pos := hp.pos
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun c uc _ _ => wp_mov fun d ud _ _ =>
    wp_add fun e1 u1 => wp_add fun e2 u2 => wp_add fun e3 u3 => wp_add fun e4 u4 =>
    wp_add fun e5 u5 => wp_add fun e6 u6 => wp_mov fun f uf _ _ => wp_add fun g' ug =>
    wp_mov fun h uh _ _ => wp_add fun i ui => wp_add fun j uj => wp_subi fun l ul _ => WP.block_nil ?_
  have x0 : d.gpr .rsi = BitVec.ofNat 64 (rr s₀) := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have x1 := u1.gpr.trans (dbl x0)
  have x2 := u2.gpr.trans (dbl x1)
  have x3 := u3.gpr.trans (dbl x2)
  have x4 := u4.gpr.trans (dbl x3)
  have x5 := u5.gpr.trans (dbl x4)
  have x6 : e6.gpr .rsi = BitVec.ofNat 64 (64 * rr s₀) := by
    rw [u6.gpr.trans (dbl x5)]; congr 1; omega
  have hm' : l.mem = saveMem s₀ := by
    rw [ul.mem, uj.mem, ui.mem, uh.mem, ug.mem, uf.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem,
      u1.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega), ?_⟩
  · rw [ul.rd, uj.rd, ui.rd, uh.rd, ug.rd, uf.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, ud.rd,
      uc.rd, ub.rd, ua.rd, hrd]
  · rw [ul.wr, uj.wr, ui.wr, uh.wr, ug.wr, uf.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, ud.wr,
      uc.wr, ub.wr, ua.wr, hwr]
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]; simp
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]; simp
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]; simp
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g]
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g, BitVec.ofNat_toNat, BitVec.setWidth_eq]; simp
  · simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other, ud.gpr, ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, x6, uf.gpr, uf.other, ug.gpr, ug.other, uh.gpr, uh.other, ui.gpr, ui.other, uj.gpr, uj.other, ul.gpr, ul.other, g, sx64]
    show _ = bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
    rw [add_ofNat, ofNat_split (a := 64) (b := 64 * rr s₀ + 64 * rr s₀) (by omega),
      show 64 * rr s₀ + 64 * rr s₀ - 64 = 128 * rr s₀ - 64 by omega,
      BitVec.add_comm (BitVec.ofNat 64 64), ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  · rw [hm']; exact (saveMem_frame s₀).mono (by simp)
  · rw [hm']; exact saveMem_saved s₀
  · rw [hm']
    show bytesAt (saveMem s₀) (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega]
    refine frame_bytesAt (saveMem_frame s₀) (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub hp (by omega))

/-! ## The loop -/

/-- The loop's condition after pair `k`. -/
theorem eval_ne {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (hz : s.zf = some (BitVec.ofNat 64 (rr s₀ - k) - 1 == 0)) :
    isa.eval .ne s = some (decide (k + 1 ≠ rr s₀)) := by
  have lt := r_lt hp
  have e : BitVec.ofNat 64 (rr s₀ - k) - 1 = BitVec.ofNat 64 (rr s₀ - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega),
      show (1 : BitVec 64).toNat = 1 from rfl]
    omega
  rw [e] at hz
  show s.zf.map (!·) = _
  rw [hz]
  by_cases hl : k + 1 = rr s₀
  · simp [hl]
  · have hne : (BitVec.ofNat 64 (rr s₀ - (k + 1)) == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have := congrArg BitVec.toNat h0
      rw [toNat_ofNat_lt (by omega)] at this
      simp at this; omega
    rw [Option.map_some, hne]; simp [hl]

theorem loop_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop (bmBody c) .ne) s (Inv s₀ (rr s₀)) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s) ?_ (rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (body_ok hS hp hk hi) fun s' ⟨hi', hz⟩ => ?_
  rw [eval_ne hp hk hz]
  by_cases hl : k + 1 = rr s₀
  · exact .inl ⟨by simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by simp [hl], rr s₀ - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  have hin : ∀ d, d + 8 ≤ 128 → ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      InRegions (t.rd ++ t.wr) (sc s₀ + BitVec.ofNat 64 d) 8 := fun d hd t hr hw => by
    rw [hr, hw, h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ hd)
  have sv : ∀ p ∈ bmSaved, s.mem.readW (sc s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1 := h.saved
  simp only [bmEpilogue, bmSaved, List.map_cons, List.map_nil]
  refine wp_movm (by rw [ea_at, h.r13]) (hin 64 (by omega) _ rfl rfl) fun a ua => ?_
  refine wp_movm (by rw [ea_at, ua.other _ (by decide), h.r13])
    (hin 72 (by omega) _ ua.rd ua.wr) fun b ub => ?_
  refine wp_movm (by rw [ea_at, ub.other _ (by decide), ua.other _ (by decide), h.r13])
    (hin 80 (by omega) _ (ub.rd.trans ua.rd) (ub.wr.trans ua.wr)) fun c uc => ?_
  refine wp_movm (by rw [ea_at, uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.r13])
    (hin 88 (by omega) _ (uc.rd.trans (ub.rd.trans ua.rd)) (uc.wr.trans (ub.wr.trans ua.wr)))
    fun d ud => ?_
  refine wp_movm (by rw [ea_at, ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), h.r13])
    (hin 96 (by omega) _ (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd)))
      (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr)))) fun e ue => ?_
  refine wp_movm (by rw [ea_at, ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r13])
    (hin 104 (by omega) _ (ue.rd.trans (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd))))
      (ue.wr.trans (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr))))) fun f uf => WP.block_nil ?_
  have hm : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  refine ⟨hm, fun r hr => ?_⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.gpr, sv (.rbx, 64) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.gpr, ua.mem, sv (.rbp, 72) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.rsp]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.gpr, ub.mem, ua.mem, sv (.r12, 80) (by simp [bmSaved])]
  · rw [uf.gpr, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, sv (.r13, 104) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.mem, ub.mem, ua.mem,
      sv (.r14, 88) (by simp [bmSaved])]
  · rw [uf.other _ (by decide), ue.gpr, ud.mem, uc.mem, ub.mem, ua.mem, sv (.r15, 96) (by simp [bmSaved])]

/-! ## The whole function -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
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

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block bmPrologue) s₀ (Inv s₀ 0) := by
  rw [prologue_eq]
  exact save_ok hp fun _ g hrd hwr hm => setup_ok hp g hrd hwr hm

theorem correct {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (blockMixWith c) s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Scrypt.blockMixX86_64.post s₀ s' := by
  unfold blockMixWith
  refine WP.seq ?_
  rw [prologue_eq]
  refine save_ok hp fun s₁ g hrd hwr hm => ?_
  refine WP.mono (setup_ok hp g hrd hwr hm) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hg'⟩ => ?_
  refine ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₃.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_y
    · exact hp.ret_s
    · exact ret_stk s₀
  · show bytesAt s'.mem (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀)
    rw [hm']
    exact post_of fun i hi => h₃.done i hi

end VG.Proof.Scrypt.X86_64.BlockMix
