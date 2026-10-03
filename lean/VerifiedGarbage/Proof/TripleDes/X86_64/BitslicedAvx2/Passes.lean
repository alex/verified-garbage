import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Pass
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Passes

/-!
# The three AVX2 passes

The loop of passes, counted down from 3 in `r11`, does to the state words
what three DES passes do (`chain`), with the components and directions of
TDEA, in every lane.
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx2

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceAvx2 VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (passW pairs swapW)
open VG.Proof.TripleDes.X86_64.Bitsliced (chain keyAt passA passD passComp passIdx_lt passAddr_eq
  keyAt_pass cnt_sub pairs_keys_congr pairs_congr swapW_congr)

/-- The key words of the passes are apart from the scratch buffer and the state. -/
theorem passKeys_apart {s : State} {S : Addr} (hS : ∀ i < 48, Apart s (S + BitVec.ofNat 64 (8 * i)))
    (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {r : Nat} (hr : r < 16) :
    Apart s (passA d p S + BitVec.ofNat 64 r * passD d p) := by
  simp only [passA, passD]
  rw [BitVec.add_assoc, passAddr_eq d p hp.1 hp.2 r hr]
  exact hS _ (passIdx_lt d p hp.1 hp.2 r hr)

structure PassesInv (d : Direction) (s₀ : State) (p : Nat) (s : State) : Prop where
  room : Room s
  ones : s.ymm ones = BitVec.allOnes 256
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pos : 1 ≤ p
  le : p ≤ 3
  words : ∀ x < 64, words s x = chain d (scheduleAt s₀.mem (s₀.gpr .rdi)) (3 - p) (words s₀) x
  count : s.gpr .r11 = BitVec.ofNat 64 p
  gpr : ∀ r, PassRegs r → s.gpr r = s₀.gpr r
  frame : Frame [spillR s₀, stateR s₀] s₀.mem s.mem

structure PassesPost (d : Direction) (s₀ s : State) : Prop where
  room : Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ x < 64, words s x = chain d (scheduleAt s₀.mem (s₀.gpr .rdi)) 3 (words s₀) x
  gpr : ∀ r, PassRegs r → s.gpr r = s₀.gpr r
  frame : Frame [spillR s₀, stateR s₀] s₀.mem s.mem

theorem passes_ok (d : Direction) {s₀ : State}
    (hS : ∀ i < 48, Apart s₀ (s₀.gpr .rdi + BitVec.ofNat 64 (8 * i)))
    (p₀ : Nat) (s₁ : State) (hs₁ : PassesInv d s₀ p₀ s₁) :
    WP isa (.loop (pass d) .ne) s₁ (PassesPost d s₀) := by
  refine WP.loop (M := isa) (PassesInv d s₀) ?_ p₀ s₁ hs₁
  intro p s hs
  let S := s₀.gpr .rdi
  have g : ∀ r, PassRegs r → s.gpr r = s₀.gpr r := hs.gpr
  have hS' : s.gpr .rdi = S := g _ (by simp [PassRegs])
  have hc := g .rcx (by simp [PassRegs])
  have hsi := g .rsi (by simp [PassRegs])
  have hp : 1 ≤ p ∧ p ≤ 3 := ⟨hs.pos, hs.le⟩
  have hk : ∀ r < 16, Apart s (passA d p (s.gpr .rdi) + BitVec.ofNat 64 r * passD d p) := by
    intro r hr
    rw [hS']
    exact (passKeys_apart hS d hp hr).congr hc hsi hs.rd hs.wr
  apply WP.mono (pass_ok d hp hs.room hs.ones hs.count hk)
  intro s' q
  have keys : ∀ r < 16, keyAt s.mem (passA d p (s.gpr .rdi)) (passD d p) r =
      VG.Proof.TripleDes.roundKey (componentSchedule (scheduleAt s₀.mem S) (passComp d p).1)
        (passComp d p).2 r := by
    intro r hr
    have e := (passKeys_apart hS d hp hr).readW hs.frame
    simp only [keyAt, hS']
    rw [e, ← keyAt_pass s₀.mem S d hp hr]; rfl
  have words' : ∀ x < 64, words s' x = chain d (scheduleAt s₀.mem S) (3 - p + 1) (words s₀) x := by
    intro x hx
    rw [q.words x hx, pairs_keys_congr 8 (fun r hr => keys r (by omega))]
    simp only [chain, show 3 - (3 - p) = p by omega]
    exact swapW_congr (pairs_congr _ 8 hs.words) x hx
  have gpr' : ∀ r, PassRegs r → s'.gpr r = s₀.gpr r := fun r hr => (q.gpr r hr).trans (g r hr)
  have frame' : Frame [spillR s₀, stateR s₀] s₀.mem s'.mem := by
    have := q.frame
    rw [show spillR s = spillR s₀ by simp only [spillR, hc],
      show stateR s = stateR s₀ by simp only [stateR, hsi]] at this
    exact hs.frame.trans this
  have cntv : s.gpr .r11 - 1 = BitVec.ofNat 64 (p - 1) := by rw [hs.count]; exact cnt_sub p hs.pos
  by_cases h1 : p = 1
  · subst h1
    left
    refine ⟨?_, q.room, q.rd.trans hs.rd, q.wr.trans hs.wr, words', gpr', frame'⟩
    show s'.zf.map (!·) = some false
    rw [q.zf, cntv]; rfl
  · right
    refine ⟨?_, p - 1, by omega, ⟨q.room, q.ones, q.rd.trans hs.rd, q.wr.trans hs.wr, by omega,
      by omega, ?_, ?_, gpr', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [q.zf, cntv]
      have : (BitVec.ofNat 64 (p - 1) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        have z : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this
        rw [z, Nat.mod_eq_of_lt (by omega)] at this
        omega
      rw [this]; rfl
    · rw [show 3 - (p - 1) = 3 - p + 1 by omega]; exact words'
    · rw [q.count, cntv]

end VG.Proof.TripleDes.X86_64.BitslicedAvx2
