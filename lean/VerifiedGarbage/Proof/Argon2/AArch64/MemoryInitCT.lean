import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitClearCT
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitLoopCT

/-! # The complete memory initialization trace depends only on public parameters -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LoopReady (memory : Addr) (lanes q : Nat) (s : State) : Prop where
  space : Space s memory (1024 * (lanes * q))
  initialized : Initialized s.mem memory lanes q 0 (bytesAt s.mem (s.gpr .x19) 64)
  destination : s.gpr .x22 = memory
  lane : s.gpr .x20 = 0
  remaining : s.gpr .x23 = BitVec.ofNat 64 lanes
  stride : s.gpr .x21 = BitVec.ofNat 64 (1024 * q)

theorem Cleared.ready {s t : State} {memory : Addr} {lanes q : Nat}
    (h : Cleared s t memory (lanes * q)) (hs : Ready memory lanes q s) :
    Ready memory lanes q t := by
  have bp := h.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide)
  have bx := h.other .x24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have sp := h.sp
  refine ⟨hs.space.same h.wr bp bx sp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.rd, h.wr, bp]; exact hs.memoryRead
  · rw [h.rd, h.wr, bp]; exact hs.lanesRead
  · rw [h.rd, h.wr, bp]; exact hs.blocksRead
  · exact (h.word hs.space (by decide)).trans hs.memoryWord
  · exact (h.word hs.space (by decide)).trans hs.lanesWord
  · exact (h.word hs.space (by decide)).trans hs.blocksWord
  · exact (h.other .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs.laneLength

theorem Setup.loopReady {s a b : State} {memory : Addr} {lanes q : Nat}
    (hs : Ready memory lanes q s) (ha : Cleared s a memory (lanes * q))
    (hb : Setup a b memory lanes q) : LoopReady memory lanes q b := by
  have ready := ha.ready hs
  refine ⟨ready.space.same hb.wr (hb.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hb.other .x24 (by decide) (by decide) (by decide) (by decide) (by decide))
    hb.sp, ?_,
    hb.destination, hb.lane, hb.remaining, hb.stride⟩
  rw [hb.mem, ha.mem]
  exact initialized_zero s.mem memory lanes q hs.space.bound _

theorem lanesSetup_rel : RelCT isa AgreeBases lanesSetupCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs publicBases)
    (fun _ _ h => h.taint) (by taint_decide)

theorem Setup.agree {s t a b : State} {memory : Addr} {lanes q : Nat}
    (ha : Setup s a memory lanes q) (hb : Setup t b memory lanes q)
    (hp : AgreeBases s t) : AgreeSaved a b := by
  refine ⟨ha.sp.trans (hp.1.trans hb.sp.symm), ?_⟩
  intro r hr
  by_cases h14 : r = .x22
  · subst r; exact ha.destination.trans hb.destination.symm
  by_cases h12 : r = .x20
  · subst r; exact ha.lane.trans hb.lane.symm
  by_cases h15 : r = .x23
  · subst r; exact ha.remaining.trans hb.remaining.symm
  by_cases h13 : r = .x21
  · subst r; exact ha.stride.trans hb.stride.symm
  have included : ∀ r ∈ savedRegs, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → r ≠ .x21 →
      r ∈ publicBases := by decide
  exact (ha.other r h14 h12 h15 h13 ((show ∀ r ∈ savedRegs, r ≠ .x15 from by decide) r hr)).trans
    ((hp.2 r (included r hr h14 h12 h15 h13)).trans (hb.other r h14 h12 h15 h13 ((show ∀ r ∈ savedRegs, r ≠ .x15 from by decide) r hr)).symm)

theorem lanesLoop_ready_rel (v : HPrime.Backend) (name : String)
    (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64)
    (hq : 2 ≤ q) :
    RelCT isa (fun s t => LoopReady memory lanes q s ∧ LoopReady memory lanes q t ∧
      AgreeSaved s t) (.loop (lane name v.hash) (.nonzero .x .x15)) AgreeSaved := by
  intro s t ts tt a b hp es et
  have initial {s : State} (h : LoopReady memory lanes q s) :
      LoopI s memory lanes q 0 (bytesAt s.mem (s.gpr .x19) 64) s :=
    ⟨by omega, by simpa using h.destination, h.lane,
      by simpa only [Nat.sub_zero] using h.remaining, h.stride, Keeps.refl _ _ _,
      h.initialized, rfl⟩
  exact lanesLoop_rel v name s t memory lanes q _ _ hp.1.space hp.2.1.space lo
    lanesBound hq _ _ _ _ _ _ ⟨initial hp.1, initial hp.2.1, hp.2.2⟩ es et

theorem code_ct (v : HPrime.Backend) (name : String)
    (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64)
    (hq : 2 ≤ q) :
    ConstantTime isa (Ready memory lanes q) AgreeBases (code name v.hash) := by
  let P := fun s t => Ready memory lanes q s ∧ Ready memory lanes q t ∧ AgreeBases s t
  have blocksPositive : 1 ≤ lanes * q := by
    have mul := Nat.mul_le_mul_right q lo
    rw [Nat.one_mul] at mul; omega
  have cleared := (clear_rel memory lanes q).wpDep (fun s t hp =>
    ⟨clear_ok s memory (lanes * q) blocksPositive hp.1.space.bound hp.1.memoryRead
        hp.1.blocksRead hp.1.memoryWord hp.1.blocksWord hp.1.space.matrix,
      clear_ok t memory (lanes * q) blocksPositive hp.2.1.space.bound hp.2.1.memoryRead
        hp.2.1.blocksRead hp.2.1.memoryWord hp.2.1.blocksWord hp.2.1.space.matrix⟩)
  let R := fun a b => AgreeBases a b ∧ ∃ s t, P s t ∧
    Cleared s a memory (lanes * q) ∧ Cleared t b memory (lanes * q)
  have setup := (lanesSetup_rel.mono (P' := R) (fun _ _ h => h.1)
    (fun _ _ h => h)).wpDep (F := fun a b => Setup a b memory lanes q) (by
    intro a b hp
    obtain ⟨_, s, t, hst, ha, hb⟩ := hp
    have ra := ha.ready hst.1
    have rb := hb.ready hst.2.1
    exact ⟨lanesSetup_ok a memory lanes q ra.memoryRead ra.lanesRead ra.memoryWord
        ra.lanesWord ra.laneLength,
      lanesSetup_ok b memory lanes q rb.memoryRead rb.lanesRead rb.memoryWord
        rb.lanesWord rb.laneLength⟩)
  have prepared : RelCT isa R lanesSetupCode (fun a b =>
      LoopReady memory lanes q a ∧ LoopReady memory lanes q b ∧ AgreeSaved a b) := setup.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, c, d, hp, ha, hb⟩ := h
    obtain ⟨pub, s, t, hst, hc, hd⟩ := hp
    exact ⟨ha.loopReady hst.1 hc, hb.loopReady hst.2.1 hd, ha.agree hb pub⟩)
  exact (cleared.seq (prepared.seq (lanesLoop_ready_rel v name memory lanes q lo
    lanesBound hq))).constantTime

end VG.Proof.Argon2.AArch64.MemoryInit
