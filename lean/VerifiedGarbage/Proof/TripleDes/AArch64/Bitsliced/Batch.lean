import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Pass
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Transpose
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64

/-!
# An AdvSIMD batch

A batch of 128 blocks, in place: each doubleword lane `q` of the 64 state
words (the 1024 bytes at `x4`) is transposed, so that lane `64 q + i` of
the words is IP of block `2 i + q`; the three passes run; the lanes are
transposed back, and each block becomes its TDEA encryption or decryption
(`batch_ok`).
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (ipLane transposeW ipLane_bit passW passW_congr tdeaW tdeaW_lane
  blockOut blockOut_cores ipLane_congr wAt)

/-! ## Doubleword lanes as blocks -/

/-- Doubleword `q` of state word `i` is block `2 i + q`. -/
theorem laneW_eq (s : State) {q i : Nat} (hq : q < 2) :
    laneW s q i = s.mem.readW (wAt (s.gpr .x4) (2 * i + q)) 64 := by
  simp only [laneW, words, vAddr]
  rw [← read16_readW, vdword_read16 _ _ hq, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    show 16 * i + 8 * q = 8 * (2 * i + q) by omega]

/-- Lane `64 q + i` of 128-bit words is lane `i` of their doublewords `q`. -/
theorem ipLane_dw {W : Nat → BitVec 128} {q i : Nat} (hi : i < 64) :
    ipLane W (64 * q + i) = ipLane (fun j => vdword (W j) q) i := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [ipLane_bit _ _ ht, ipLane_bit _ _ ht, getLsbD_vdword _ hi]

/-! ## The passes -/

/-- What the passes leave. -/
structure PassesPost (d : Direction) (s s' : State) : Prop where
  room : Room s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  words : ∀ x < 64, words s' x = tdeaW (scheduleAt s.mem (s.gpr .x0)) d (words s) x
  gpr : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → s'.gpr r = s.gpr r
  frame : Frame [stateR s] s.mem s'.mem

/-- A pass, followed by what is left of the passes, `Q`, of its result. -/
theorem pass_then {c : Nat} (hc : c < 3) (d : Direction) {s : State} (h : Room s)
    (hz : s.v zeroReg = 0) (hS : Sched s) {p : Prog isa} {Q : State → Prop}
    (k : ∀ s', PassPost c d s s' → WP isa p s' Q) : WP isa (.seq (pass c d) p) s Q :=
  WP.seq (WP.mono (pass_ok hc d h hz hS) k)

theorem PassPost.sched {c : Nat} {d : Direction} {s s' : State} (p : PassPost c d s s')
    (hS : Sched s) : Sched s' :=
  hS.congr (p.gpr _ (by decide) (by decide) (by decide)) (p.gpr _ (by decide) (by decide) (by decide))
    p.rd p.wr

theorem PassPost.schedule {c : Nat} {d : Direction} {s s' : State} (p : PassPost c d s s')
    (hS : Sched s) : scheduleAt s'.mem (s'.gpr .x0) = scheduleAt s.mem (s.gpr .x0) := by
  rw [p.gpr _ (by decide) (by decide) (by decide)]
  exact VG.Proof.TripleDes.scheduleAt_eq_of_frame _ p.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hS.sep

theorem PassPost.state {c : Nat} {d : Direction} {s s' : State} (p : PassPost c d s s') :
    stateR s' = stateR s := by
  simp only [stateR, p.gpr .x4 (by decide) (by decide) (by decide)]

theorem passes_ok (d : Direction) {s : State} (h : Room s) (hz : s.v zeroReg = 0)
    (hS : Sched s) : WP isa (passes d) s (PassesPost d s) := by
  cases d with
  | encrypt =>
    refine pass_then (by decide) .encrypt h hz hS fun s₁ p₁ => ?_
    refine pass_then (by decide) .decrypt p₁.room p₁.zero (p₁.sched hS) fun s₂ p₂ => ?_
    apply WP.mono (pass_ok (by decide) .encrypt p₂.room p₂.zero (p₂.sched (p₁.sched hS)))
    intro s₃ p₃
    have K₁ := p₁.schedule hS
    have K₂ := p₂.schedule (p₁.sched hS)
    refine ⟨p₃.room, p₃.rd.trans (p₂.rd.trans p₁.rd), p₃.wr.trans (p₂.wr.trans p₁.wr),
      p₃.sp.trans (p₂.sp.trans p₁.sp), fun x hx => ?_,
      fun r a b c => (p₃.gpr r a b c).trans ((p₂.gpr r a b c).trans (p₁.gpr r a b c)), ?_⟩
    · rw [p₃.words x hx, K₂, K₁]
      exact passW_congr _ _ (fun y hy => by
        rw [p₂.words y hy, K₁]; exact passW_congr _ _ p₁.words y hy) x hx
    · have f₂ := p₂.frame
      rw [p₁.state] at f₂
      have f₃ := p₃.frame
      rw [p₂.state, p₁.state] at f₃
      exact p₁.frame.trans (f₂.trans f₃)
  | decrypt =>
    refine pass_then (by decide) .decrypt h hz hS fun s₁ p₁ => ?_
    refine pass_then (by decide) .encrypt p₁.room p₁.zero (p₁.sched hS) fun s₂ p₂ => ?_
    apply WP.mono (pass_ok (by decide) .decrypt p₂.room p₂.zero (p₂.sched (p₁.sched hS)))
    intro s₃ p₃
    have K₁ := p₁.schedule hS
    have K₂ := p₂.schedule (p₁.sched hS)
    refine ⟨p₃.room, p₃.rd.trans (p₂.rd.trans p₁.rd), p₃.wr.trans (p₂.wr.trans p₁.wr),
      p₃.sp.trans (p₂.sp.trans p₁.sp), fun x hx => ?_,
      fun r a b c => (p₃.gpr r a b c).trans ((p₂.gpr r a b c).trans (p₁.gpr r a b c)), ?_⟩
    · rw [p₃.words x hx, K₂, K₁]
      exact passW_congr _ _ (fun y hy => by
        rw [p₂.words y hy, K₁]; exact passW_congr _ _ p₁.words y hy) x hx
    · have f₂ := p₂.frame
      rw [p₁.state] at f₂
      have f₃ := p₃.frame
      rw [p₂.state, p₁.state] at f₃
      exact p₁.frame.trans (f₂.trans f₃)

/-! ## The batch -/

structure BatchPost (d : Direction) (s s' : State) : Prop where
  out : ∀ b < 128, blockAt s'.mem (wAt (s.gpr .x4) b) =
    blockOut (scheduleAt s.mem (s.gpr .x0)) d (blockAt s.mem (wAt (s.gpr .x4) b))
  gpr : ∀ r, r ≠ .x5 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [stateR s] s.mem s'.mem

theorem batch_ok (d : Direction) {s : State} (h : Room s) (hS : Sched s) :
    WP isa (batch d) s (BatchPost d s) := by
  let S := s.gpr .x0
  let D := s.gpr .x4
  rw [batch]
  apply WP.seq
  -- the transposition, and zero
  obtain ⟨s₁, run₁, w₁, g₁, -, sp₁, rd₁, wr₁, f₁⟩ := transpose_ok h
  let s₂ := s₁.setV zeroReg 0
  refine WP.of_runBlock ⟨s₂, runBlock_cat_some run₁ (by
    rw [runBlock_cons]; exact (by rfl : runStep isa (some s₂) [] = some s₂)), ?_⟩
  have g₂ : ∀ r, r ≠ .x10 → s₂.gpr r = s.gpr r := g₁
  have h₂ : Room s₂ := room_congr h (g₂ _ (by decide)) wr₁
  have S₂ : Sched s₂ := hS.congr (g₂ _ (by decide)) (g₂ _ (by decide)) rd₁ wr₁
  have st₂ : stateR s₂ = stateR s := by simp only [stateR, g₂ .x4 (by decide)]
  apply WP.seq
  apply WP.mono (passes_ok d h₂ (v_setV_self _ _ _) S₂)
  intro s₃ q₃
  have g₃ : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x7 → r ≠ .x10 → s₃.gpr r = s.gpr r :=
    fun r a b c e => (q₃.gpr r a b c).trans (g₂ r e)
  -- the transposition back
  obtain ⟨s₄, run₄, w₄, g₄, -, sp₄, rd₄, wr₄, f₄⟩ := transpose_ok q₃.room
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have si₄ : s₄.gpr .x4 = D :=
    (g₄ .x4 (by decide)).trans (g₃ _ (by decide) (by decide) (by decide) (by decide))
  have K₂ : scheduleAt s₂.mem (s₂.gpr .x0) = scheduleAt s.mem S := by
    rw [g₂ _ (by decide)]
    exact VG.Proof.TripleDes.scheduleAt_eq_of_frame S f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hS.sep
  refine ⟨fun b hb => ?_, fun r a c e f => by rw [g₄ r f, g₃ r e a c f], rd₄.trans (q₃.rd.trans rd₁),
    wr₄.trans (q₃.wr.trans wr₁), sp₄.trans (q₃.sp.trans sp₁), ?_⟩
  · have hq : b % 2 < 2 := Nat.mod_lt _ (by decide)
    have hi : b / 2 < 64 := by omega
    have eb : 2 * (b / 2) + b % 2 = b := Nat.div_add_mod b 2
    -- lane 64 q + i before the passes: IP of the block
    have lane₂ : ipLane (words s₂) (64 * (b % 2) + b / 2) =
        permute ip (decodeBlock (blockAt s.mem (wAt D b))) := by
      rw [ipLane_dw hi]
      have e : ∀ j < 64, vdword (words s₂ j) (b % 2) = transposeW (laneW s (b % 2)) j := by
        intro j hj; exact w₁ _ hq j hj
      rw [ipLane_congr e]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hi fun j hj => ?_
      rw [laneW_eq s hq, eb]
      exact readW_bit s.mem (wAt D b) hj
    -- the block's word at the end
    have word₄ : s₄.mem.readW (wAt D b) 64 = transposeW (laneW s₃ (b % 2)) (b / 2) := by
      rw [← w₄ _ hq _ hi, laneW_eq s₄ hq, si₄, eb]
    rw [blockOut_cores, ← K₂]
    apply blockAt_of_readW
    intro j hj
    rw [word₄, VG.Proof.TripleDes.Bitslice.transpose_out _ _ j hj]
    have e₃ : ipLane (laneW s₃ (b % 2)) (b / 2) = ipLane (words s₃) (64 * (b % 2) + b / 2) :=
      (ipLane_dw hi).symm
    rw [e₃, ipLane_congr q₃.words, tdeaW_lane _ d _ (by omega), lane₂]
  · have a : Frame [stateR s] s.mem s₂.mem := f₁
    have b : Frame [stateR s] s₂.mem s₃.mem := by rw [← st₂]; exact q₃.frame
    have c : Frame [stateR s] s₃.mem s₄.mem := by
      rw [show stateR s₃ = stateR s by
        simp only [stateR, g₃ .x4 (by decide) (by decide) (by decide) (by decide)]] at f₄
      exact f₄
    exact (a.trans b).trans c

end VG.Proof.TripleDes.AArch64.BitslicedNeon
