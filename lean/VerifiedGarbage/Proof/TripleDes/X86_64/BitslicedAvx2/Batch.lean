import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Passes
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Batch

/-!
# An AVX2 batch

A batch of 256 blocks, in place: each quadword lane `q` of the 64 state
words (the 2048 bytes at `rsi`) is transposed, so that lane `64 q + i` of
the words is IP of block `4 i + q`; the three passes run; the lanes are
transposed back, and each block becomes its TDEA encryption or decryption
(`batch_ok`).
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx2

open VG VG.X86_64 VG.X86_64.StraightY VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceAvx2
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (ipLane transposeW ipLane_bit)
open VG.Proof.TripleDes.X86_64.Bitsliced (chain chain_lane blockOut blockOut_cores ipLane_congr wAt
  readW_bit blockAt_of_readW)

/-! ## Quadword lanes as blocks -/

theorem qw_readW (m : Mem) (a : Addr) {q : Nat} (hq : q < 4) :
    qw (m.readW a 256) q = m.readW (a + BitVec.ofNat 64 q * 8) 64 := by
  have e := readW_extract m a (w := 256) (k := 8 * q) (n := 8) (by omega)
  rw [show 8 * (8 * q) = 64 * q by omega, show 8 * 8 = 64 by rfl] at e
  rw [qw, e]
  congr 2
  rw [BitVec.mul_comm, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_mul_ofNat]

/-- Quadword `q` of state word `i` is block `4 i + q`. -/
theorem laneW_eq (s : State) {q i : Nat} (hq : q < 4) :
    laneW s q i = s.mem.readW (wAt (s.gpr .rsi) (4 * i + q)) 64 := by
  simp only [laneW, words, yAddr]
  rw [qw_readW _ _ hq, BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  have e : ∀ a b : Nat, a = b → s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 a) 64 =
      s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 b) 64 := fun a b h => by rw [h]
  exact e _ _ (by omega)

/-- Lane `64 q + i` of 256-bit words is lane `i` of their quadwords `q`. -/
theorem ipLane_qw {W : Nat → BitVec 256} {q i : Nat} (hi : i < 64) :
    ipLane W (64 * q + i) = ipLane (fun j => qw (W j) q) i := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [ipLane_bit _ _ ht, ipLane_bit _ _ ht, getLsbD_qw _ hi]

/-! ## The batch -/

/-- What a batch needs: the scratch buffer and the 256 blocks' state words,
and the schedule's words, readable and apart from both. -/
structure BatchPre (s : State) : Prop where
  room : Room s
  sched : ∀ i < 48, Apart s (s.gpr .rdi + BitVec.ofNat 64 (8 * i))
  schedSep : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint (stateR s)

structure BatchPost (d : Direction) (s s' : State) : Prop where
  out : ∀ b < 256, blockAt s'.mem (wAt (s.gpr .rsi) b) =
    blockOut (scheduleAt s.mem (s.gpr .rdi)) d (blockAt s.mem (wAt (s.gpr .rsi) b))
  rsi : s'.gpr .rsi = s.gpr .rsi + 2048
  rdx : s'.gpr .rdx = s.gpr .rdx - 256
  cf : s'.cf = some (decide ((s.gpr .rdx - 256).toNat < 256))
  gpr : ∀ r, PassRegs r → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [spillR s, stateR s] s.mem s'.mem

theorem frame_into {rs : List Region} {m m' : Mem} {r : Region} (h : Frame [r] m m') (hr : r ∈ rs) :
    Frame rs m m' :=
  h.mono fun r' h' => by simp only [List.mem_singleton] at h'; subst h'; exact hr

theorem batch_ok (d : Direction) {s : State} (h : BatchPre s) : WP isa (batch d) s (BatchPost d s) := by
  let S := s.gpr .rdi
  let D := s.gpr .rsi
  rw [batch]
  apply WP.seq
  -- the transposition, all ones, and the count of passes
  obtain ⟨s₁, run₁, w₁, g₁, -, -, rd₁, wr₁, f₁⟩ := transpose_ok h.room.state
  let t₁ := s₁.setReg .rbx (BitVec.allOnes 64)
  let t₂ := (VOp.vmovq ones .rbx).exec t₁
  let t₃ := (VOp.vpbroadcastq .l256 ones ones).exec t₂
  let s₂ := t₃.setReg .r11 ((3 : BitVec 32).signExtend 64)
  refine WP.of_runBlock ⟨s₂, runBlock_cat_some (runBlock_cat_some run₁ (by
    rw [bcast, runBlock_cons, show exec (.movImm64 .rbx (BitVec.allOnes 64)) s₁ = some t₁ from rfl,
      runStep_some, runBlock_cons, show exec (.vop (.vmovq ones .rbx)) t₁ = some t₂ from rfl,
      runStep_some, runBlock_cons,
      show exec (.vop (.vpbroadcastq .l256 ones ones)) t₂ = some t₃ from rfl, runStep_some,
      runBlock_nil])) (by rw [runBlock_cons]; rfl), ?_⟩
  have ones₂ : s₂.ymm ones = BitVec.allOnes 256 :=
    bcast_mask t₁ ones .rbx true (by simp [t₁, gpr_setReg, maskVal])
  have g₂ : ∀ r, r ≠ .rbx → r ≠ .r11 → s₂.gpr r = s.gpr r := by
    intro r a b
    simp [s₂, t₃, t₂, t₁, gpr_setReg, a, b, g₁ r a]
  have m₂ : s₂.mem = s₁.mem := by simp [s₂, t₃, t₂, t₁, mem_setReg]
  have rd₂ : s₂.rd = s.rd := by simp [s₂, t₃, t₂, t₁, rd_setReg, rd₁]
  have wr₂ : s₂.wr = s.wr := by simp [s₂, t₃, t₂, t₁, wr_setReg, wr₁]
  have c₂ := g₂ .rcx (by decide) (by decide)
  have si₂ := g₂ .rsi (by decide) (by decide)
  have di₂ := g₂ .rdi (by decide) (by decide)
  have h₂ : Room s₂ := h.room.congr c₂ si₂ wr₂
  have words₂ : ∀ j, words s₂ j = words s₁ j := fun j => by
    simp only [words, m₂, si₂, g₁ .rsi (by decide)]
  have scr₂ : spillR s₂ = spillR s := by simp only [spillR, c₂]
  have st₂ : stateR s₂ = stateR s := by simp only [stateR, si₂]
  have f₂ : Frame [spillR s, stateR s] s.mem s₂.mem := by
    rw [m₂]; exact frame_into f₁ (List.mem_cons_of_mem _ List.mem_cons_self)
  -- the passes
  apply WP.seq
  have hS₂ : ∀ i < 48, Apart s₂ (s₂.gpr .rdi + BitVec.ofNat 64 (8 * i)) := by
    intro i hi; rw [di₂]; exact (h.sched i hi).congr c₂ si₂ rd₂ wr₂
  have inv : PassesInv d s₂ 3 s₂ :=
    ⟨h₂, ones₂, rfl, rfl, by decide, by decide, fun _ _ => rfl, by simp [s₂, gpr_setReg],
      fun _ _ => rfl, Frame.refl _ _⟩
  apply WP.mono (passes_ok d hS₂ 3 s₂ inv)
  intro s₃ q₃
  have g₃ : ∀ r, PassRegs r → s₃.gpr r = s.gpr r := by
    intro r hr; rw [q₃.gpr r hr, g₂ r hr.2.1 hr.2.2.2.2.2]
  have si₃ := g₃ .rsi (by simp [PassRegs])
  have c₃ := g₃ .rcx (by simp [PassRegs])
  have rdx₃ := g₃ .rdx (by simp [PassRegs])
  -- the transposition back, and the next batch
  obtain ⟨s₄, run₄, w₄, g₄, -, -, rd₄, wr₄, f₄⟩ := transpose_ok q₃.room.state
  have si₄ : s₄.gpr .rsi = D := (g₄ .rsi (by decide)).trans si₃
  have rdx₄ : s₄.gpr .rdx = s.gpr .rdx := (g₄ .rdx (by decide)).trans rdx₃
  let u₁ := (arithFlags s₄ (s₄.gpr .rsi + (2048 : BitVec 32).signExtend 64)
    (decide (2 ^ 64 ≤ (s₄.gpr .rsi).toNat + ((2048 : BitVec 32).signExtend 64).toNat))
    (addOverflow (s₄.gpr .rsi) ((2048 : BitVec 32).signExtend 64)
      (s₄.gpr .rsi + (2048 : BitVec 32).signExtend 64))).setReg .rsi
    (s₄.gpr .rsi + (2048 : BitVec 32).signExtend 64)
  let v := u₁.gpr .rdx - (256 : BitVec 32).signExtend 64
  let u₂ := (arithFlags u₁ v (decide ((u₁.gpr .rdx).toNat < ((256 : BitVec 32).signExtend 64).toNat))
    (subOverflow (u₁.gpr .rdx) ((256 : BitVec 32).signExtend 64) v)).setReg .rdx v
  let s₅ := cmpState u₂ .rdx 256
  refine WP.of_runBlock ⟨s₅, runBlock_cat_some run₄ (by
    rw [runBlock_cons, show exec (.alu .add .rsi (.imm 2048)) s₄ = some u₁ from rfl, runStep_some,
      runBlock_cons, show exec (.alu .sub .rdx (.imm 256)) u₁ = some u₂ from rfl, runStep_some,
      cmp_run]), ?_⟩
  have m₅ : s₅.mem = s₄.mem := by simp [s₅, cmpState, u₂, u₁, mem_setReg, mem_arithFlags]
  have g₅ : ∀ r, r ≠ .rsi → r ≠ .rdx → s₅.gpr r = s₄.gpr r := by
    intro r a b; simp [s₅, cmpState, u₂, u₁, gpr_setReg, a, b]
  have rdx₅ : s₅.gpr .rdx = s.gpr .rdx - 256 := by
    simp [s₅, cmpState, u₂, u₁, gpr_setReg, v, rdx₄]
  -- every block of the batch
  have K₂ : scheduleAt s₂.mem (s₂.gpr .rdi) = scheduleAt s.mem S := by
    rw [di₂, m₂]
    exact VG.Proof.TripleDes.scheduleAt_eq_of_frame S f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.schedSep
  refine ⟨fun b hb => ?_, ?_, rdx₅, ?_, fun r hr a c => ?_, ?_, ?_, ?_⟩
  · have hq : b % 4 < 4 := Nat.mod_lt _ (by decide)
    have hi : b / 4 < 64 := by omega
    have eb : 4 * (b / 4) + b % 4 = b := Nat.div_add_mod b 4
    -- lane 64 q + i before the passes: IP of the block
    have lane₂ : ipLane (words s₂) (64 * (b % 4) + b / 4) =
        permute ip (decodeBlock (blockAt s.mem (wAt D b))) := by
      rw [ipLane_qw hi]
      have e : ∀ j < 64, qw (words s₂ j) (b % 4) = transposeW (laneW s (b % 4)) j := by
        intro j hj; rw [words₂]; exact w₁ _ hq j hj
      rw [ipLane_congr e]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hi fun j hj => ?_
      rw [laneW_eq s hq, eb]
      exact readW_bit s.mem (wAt D b) hj
    -- the block's word at the end
    have word₅ : s₅.mem.readW (wAt D b) 64 = transposeW (laneW s₃ (b % 4)) (b / 4) := by
      rw [m₅, ← w₄ _ hq _ hi, laneW_eq s₄ hq, si₄, eb]
    rw [blockOut_cores, ← K₂]
    apply blockAt_of_readW
    intro j hj
    rw [word₅, VG.Proof.TripleDes.Bitslice.transpose_out _ _ j hj]
    have e₃ : ipLane (laneW s₃ (b % 4)) (b / 4) = ipLane (words s₃) (64 * (b % 4) + b / 4) :=
      (ipLane_qw hi).symm
    rw [e₃, ipLane_congr q₃.words, chain_lane d _ _ (by omega), lane₂]
    rfl
  · simp [s₅, cmpState, u₂, u₁, gpr_setReg, si₄]; rfl
  · have u₂d : u₂.gpr .rdx = s.gpr .rdx - 256 := by
      simp [u₂, u₁, gpr_setReg, v, rdx₄]
    simp only [s₅, cmpState, cf_arithFlags, u₂d,
      show ((256 : BitVec 32).signExtend 64).toNat = 256 by decide]
  · rw [g₅ r a c, g₄ r hr.2.1, g₃ r hr]
  · simp [s₅, cmpState, u₂, u₁, rd_setReg, rd_arithFlags, rd₄, q₃.rd, rd₂]
  · simp [s₅, cmpState, u₂, u₁, wr_setReg, wr_arithFlags, wr₄, q₃.wr, wr₂]
  · have a := q₃.frame
    rw [scr₂, st₂] at a
    have b : Frame [spillR s, stateR s] s₃.mem s₄.mem := by
      rw [show stateR s₃ = stateR s by simp only [stateR, si₃]] at f₄
      exact frame_into f₄ (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [m₅]
    exact (f₂.trans a).trans b

end VG.Proof.TripleDes.X86_64.BitslicedAvx2
