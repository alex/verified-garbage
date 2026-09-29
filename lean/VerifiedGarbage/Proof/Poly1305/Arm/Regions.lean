import VerifiedGarbage.Proof.Poly1305.Arm.Bytes

/-!
# Poly1305 on 32-bit ARM: which parts of the state the code writes

Untrusted: everything here is checked by Lean. Lists of ranges of the state
(`offR`), the frames of writes into them, and what they leave unchanged: the
key, the saved registers, the limbs of `r` and the stored accumulator.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt)

/-- The ranges `[a, a + len)` of the state at `B`, for `(a, len)` in `l`. -/
def offR (B : Addr) (l : List (Nat × Nat)) : List Region := l.map fun p => ⟨B + BitVec.ofNat 64 p.1, p.2⟩

/-- A range disjoint from each of the ranges `l`. -/
theorem dj_offR (B : Addr) {d n : Nat} {l : List (Nat × Nat)}
    (h : (l.all fun p => d + n ≤ p.1 ∨ p.1 + p.2 ≤ d) = true)
    (hb : d + n < 2 ^ 32) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    ∀ r ∈ offR B l, (⟨B + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  have h1 := List.all_eq_true.mp h p hp
  have h2 := List.all_eq_true.mp hl p hp
  simp only [decide_eq_true_eq] at h1 h2
  exact disjoint_sub B h1 hb h2

/-- Each of the ranges `l` is inside one of the ranges `l'`. -/
theorem sub_offR (B : Addr) {l l' : List (Nat × Nat)}
    (h : (l.all fun p => l'.any fun q => q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) = true)
    (hl : (l'.all fun q => q.1 + q.2 < 2 ^ 32) = true) :
    ∀ r ∈ offR B l, ∃ r' ∈ offR B l', Region.Sub r r' := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  obtain ⟨q, hq, h1⟩ := List.any_eq_true.mp (List.all_eq_true.mp h p hp)
  have h2 := List.all_eq_true.mp hl q hq
  simp only [decide_eq_true_eq] at h1 h2
  exact ⟨_, List.mem_map.mpr ⟨q, hq, rfl⟩, sub_sub B h1.1 h1.2 h2⟩

theorem _root_.VG.Frame.offR_sub {B : Addr} {l l' : List (Nat × Nat)} {m m' : Mem} (hf : Frame (offR B l) m m')
    (h : (l.all fun p => l'.any fun q => q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) = true)
    (hl : (l'.all fun q => q.1 + q.2 < 2 ^ 32) = true) : Frame (offR B l') m m' :=
  hf.sub (sub_offR B h hl)

/-- A write inside one of the ranges. -/
theorem _root_.VG.Frame.writeOff {B : Addr} {l : List (Nat × Nat)} {m m' : Mem} (hf : Frame (offR B l) m m')
    {a len d n : Nat} (hm : (a, len) ∈ l) (h1 : a ≤ d) (h2 : d + n ≤ a + len) (h3 : a + len < 2 ^ 32)
    {w : Nat} (v : BitVec w) (hw : w / 8 = n) :
    Frame (offR B l) m (m'.writeW (B + BitVec.ofNat 64 d) v) :=
  hf.writeW (List.mem_map.mpr ⟨_, hm, rfl⟩) v (hw ▸ contains_sub B h1 h2 h3)

theorem offR_one (B : Addr) (a len : Nat) : offR B [(a, len)] = [⟨B + BitVec.ofNat 64 a, len⟩] := rfl

theorem accR_offR (B : Addr) : [accR B] = offR B [(0, 20)] := by simp [offR]

theorem _root_.VG.Frame.word {B : Addr} {l : List (Nat × Nat)} {m m' : Mem} (hf : Frame (offR B l) m m') {d : Nat}
    (h : (l.all fun p => d + 4 ≤ p.1 ∨ p.1 + p.2 ≤ d) = true) (hb : d + 4 < 2 ^ 32)
    (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    m'.readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  hf.readW (Region.contains_self _ _) (dj_offR B h hb hl) (by decide)

/-! ## What the writes leave -/

theorem Saved.frame {B : Addr} {g : Reg → BitVec 32} {m m' : Mem} (hs : Saved B g m) {l : List (Nat × Nat)}
    (hf : Frame (offR B l) m m') (h : (l.all fun p => 88 ≤ p.1 ∨ p.1 + p.2 ≤ 56) = true)
    (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) : Saved B g m' := fun i hi => by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => (dj_offR B (d := 56) (n := 32) h (by omega) hl r hr).sub_left
    (sub_sub B (by omega) (by omega) (by omega))) (by decide)]
  exact hs i hi

theorem rval_frame' {B : Addr} {m m' : Mem} {l : List (Nat × Nat)} (hf : Frame (offR B l) m m')
    (h : (l.all fun p => 124 ≤ p.1 ∨ p.1 + p.2 ≤ 88) = true) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true)
    {i : Nat} (hi : i < 10) : rval m' B i = rval m B i := by
  have hro := rOff_lt i hi
  have h88 : 88 ≤ rOff i := by
    have : ∀ i < 10, 88 ≤ rOff i := by decide
    exact this i hi
  have hd : ∀ n, rOff i + n ≤ 124 → ∀ r ∈ offR B l, (⟨B + BitVec.ofNat 64 (rOff i), n⟩ : Region).Disjoint r :=
    fun n hn r hr => (dj_offR B (d := 88) (n := 36) h (by omega) hl r hr).sub_left
      (sub_sub B (by omega) (by omega) (by omega))
  have hb : ∀ i < 10, rOff i + 1 ≤ 124 := by decide
  have hw : ∀ i < 10, ¬(i = 4 ∨ i = 9) → rOff i + 4 ≤ 124 := by decide
  simp only [rval]
  split
  · rename_i h49
    congr 1
    exact hf _ fun r hr hc => hd 1 (hb i hi) r hr _ ((Region.contains_self _ _).byte (by simp)) hc
  · rename_i h49
    rw [hf.readW (Region.contains_self _ _) (hd 4 (hw i hi h49)) (by decide)]

theorem rlimb_frame' {B : Addr} {m m' : Mem} {l : List (Nat × Nat)} (hf : Frame (offR B l) m m')
    (h : (l.all fun p => 40 ≤ p.1 ∨ p.1 + p.2 ≤ 24) = true) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    rlimb m' B = rlimb m B :=
  rlimb_frame fun i hi => hf.readW (Region.contains_self _ _) (fun r hr =>
    (dj_offR B (d := 24) (n := 16) h (by omega) hl r hr).sub_left (sub_sub B (by omega) (by omega) (by omega)))
    (by decide)

theorem accD_frame {B : Addr} {m m' : Mem} {l : List (Nat × Nat)} (hf : Frame (offR B l) m m')
    (h : (l.all fun p => 20 ≤ p.1) = true) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    accD m' B = accD m B := by
  have hw : ∀ i < 5, hwd m' B i = hwd m B i := fun i hi => by
    simp only [hwd]
    rw [hf.readW (Region.contains_self _ _) (fun r hr =>
      (dj_offR B (d := 0) (n := 20) (by
        rw [List.all_eq_true] at h ⊢
        intro p hp; have := h p hp; simp only [decide_eq_true_eq] at this ⊢; omega) (by omega) hl r hr).sub_left
      (sub_sub B (by omega) (by omega) (by omega))) (by decide)]
  funext k
  simp only [accD, hw 0 (by omega), hw 1 (by omega), hw 2 (by omega), hw 3 (by omega), hw 4 (by omega)]

/-- The key's bytes. -/
theorem key_frame {B : Addr} {m m' : Mem} {l : List (Nat × Nat)} (hf : Frame (offR B l) m m')
    (h : (l.all fun p => 56 ≤ p.1 ∨ p.1 + p.2 ≤ 24) = true) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    bytesAt m' (B + 24) 32 = bytesAt m (B + 24) 32 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hd := dj_offR B (d := 24) (n := 32) h (by omega) hl
  rw [show (24 : Addr) = BitVec.ofNat 64 24 from rfl] at *
  exact hf.bytes (R := ⟨B + BitVec.ofNat 64 24, 32⟩) hd (by simp) (List.mem_range.mp hi)

/-! ## The stored accumulator -/

/-- The accumulator's limbs, if it is below `p`. -/
theorem val_accD_eq {m : Mem} {B : Addr} (h : leNum (bytesAt m B 24) < P) :
    val (accD m B) = leNum (bytesAt m B 24) := by
  rw [val_accD, leNum_bytesAt_24] at *
  simp only [hwd, Nat.mul_zero, Nat.reduceMul] at *
  simp only [P] at h
  omega

end VG.Proof.Poly1305.Arm
