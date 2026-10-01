import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Cmac.Block

/-!
# CMAC: blocks formed a 32-bit word at a time

Untrusted: everything here is checked by Lean. What the 32-bit targets'
stores leave: the XOR of two blocks stored a word at a time (`xor4Mem`; the
block written may be one of those read, as long as no word written is read
afterwards, `Sep4`), a zeroed block (`zero4`), and a counter block `C = P ⊕ Q`
with `P` zeroed (`chainMem4`).
-/

namespace VG.Proof.Cmac

open VG

/-- No word written at `c` is read at `p` after it: the word `i` written is
disjoint from every word `j > i` of `p`. -/
def Sep4 (c p : Addr) : Prop :=
  ∀ i < 4, ∀ j < 4, i < j → (⟨c + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 (4 * j), 4⟩

theorem Sep4.self (c : Addr) : Sep4 c c := fun i hi j hj hij =>
  Offset.disjoint c (by omega) (by omega) (by omega)

theorem Sep4.of_disjoint {c p : Addr} (h : (⟨c, 16⟩ : Region).Disjoint ⟨p, 16⟩) : Sep4 c p :=
  fun i hi j hj _ => (h.sub_left (Offset.sub_base c (by omega))).sub_right (Offset.sub_base p (by omega))

theorem readW_writeW_disj {m : Mem} {a b : Addr} (v : BitVec 32) (h : (⟨a, 4⟩ : Region).Disjoint ⟨b, 4⟩) :
    (m.writeW a v).readW b 32 = m.readW b 32 :=
  Mem.readW_writeW_sep (h.symm.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)

/-- The memory after storing at `c` the XOR of the blocks at `p` and `q`, a
word at a time. -/
def xor4Mem (m : Mem) (c p q : Addr) : Mem :=
  let m₁ := m.writeW c (m.readW p 32 ^^^ m.readW q 32)
  let m₂ := m₁.writeW (c + BitVec.ofNat 64 4)
    (m₁.readW (p + BitVec.ofNat 64 4) 32 ^^^ m₁.readW (q + BitVec.ofNat 64 4) 32)
  let m₃ := m₂.writeW (c + BitVec.ofNat 64 8)
    (m₂.readW (p + BitVec.ofNat 64 8) 32 ^^^ m₂.readW (q + BitVec.ofNat 64 8) 32)
  m₃.writeW (c + BitVec.ofNat 64 12) (m₃.readW (p + BitVec.ofNat 64 12) 32 ^^^ m₃.readW (q + BitVec.ofNat 64 12) 32)

theorem xor4Mem_eq (m : Mem) {c p q : Addr} (hp : Sep4 c p) (hq : Sep4 c q) :
    xor4Mem m c p q = store4 m c (m.readW p 32 ^^^ m.readW q 32)
      (m.readW (p + BitVec.ofNat 64 4) 32 ^^^ m.readW (q + BitVec.ofNat 64 4) 32)
      (m.readW (p + BitVec.ofNat 64 8) 32 ^^^ m.readW (q + BitVec.ofNat 64 8) 32)
      (m.readW (p + BitVec.ofNat 64 12) 32 ^^^ m.readW (q + BitVec.ofNat 64 12) 32) := by
  have e (x : Addr) (h : Sep4 c x) (i j : Nat) (hi : i < 4) (hj : j < 4) (hij : i < j) :
      (⟨c + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint ⟨x + BitVec.ofNat 64 (4 * j), 4⟩ := h i hi j hj hij
  have p01 : (⟨c, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 4, 4⟩ := by simpa using e p hp 0 1 (by decide) (by decide) (by decide)
  have q01 : (⟨c, 4⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 4, 4⟩ := by simpa using e q hq 0 1 (by decide) (by decide) (by decide)
  have p02 : (⟨c, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 8, 4⟩ := by simpa using e p hp 0 2 (by decide) (by decide) (by decide)
  have q02 : (⟨c, 4⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 8, 4⟩ := by simpa using e q hq 0 2 (by decide) (by decide) (by decide)
  have p03 : (⟨c, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 12, 4⟩ := by simpa using e p hp 0 3 (by decide) (by decide) (by decide)
  have q03 : (⟨c, 4⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 12, 4⟩ := by simpa using e q hq 0 3 (by decide) (by decide) (by decide)
  have p12 : (⟨c + BitVec.ofNat 64 4, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 8, 4⟩ := e p hp 1 2 (by decide) (by decide) (by decide)
  have q12 : (⟨c + BitVec.ofNat 64 4, 4⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 8, 4⟩ := e q hq 1 2 (by decide) (by decide) (by decide)
  have p13 : (⟨c + BitVec.ofNat 64 4, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 12, 4⟩ := e p hp 1 3 (by decide) (by decide) (by decide)
  have q13 : (⟨c + BitVec.ofNat 64 4, 4⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 12, 4⟩ := e q hq 1 3 (by decide) (by decide) (by decide)
  have p23 : (⟨c + BitVec.ofNat 64 8, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 12, 4⟩ := e p hp 2 3 (by decide) (by decide) (by decide)
  have q23 : (⟨c + BitVec.ofNat 64 8, 4⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 12, 4⟩ := e q hq 2 3 (by decide) (by decide) (by decide)
  simp only [xor4Mem, store4, readW_writeW_disj _ p01, readW_writeW_disj _ q01, readW_writeW_disj _ p02,
    readW_writeW_disj _ q02, readW_writeW_disj _ p03, readW_writeW_disj _ q03, readW_writeW_disj _ p12,
    readW_writeW_disj _ q12, readW_writeW_disj _ p13, readW_writeW_disj _ q13, readW_writeW_disj _ p23,
    readW_writeW_disj _ q23]

theorem xor4Mem_frame (m : Mem) (c p q : Addr) : Frame [⟨c, 16⟩] m (xor4Mem m c p q) := by
  have k (d : Nat) (h : d + 4 ≤ 16) : (⟨c, 16⟩ : Region).Contains (c + BitVec.ofNat 64 d) 4 :=
    Offset.contains_base c h (by omega)
  have k0 : (⟨c, 16⟩ : Region).Contains c 4 := by simpa using k 0 (by decide)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ k0).writeW (List.mem_singleton_self _) _
    (k 4 (by decide))).writeW (List.mem_singleton_self _) _ (k 8 (by decide))).writeW
    (List.mem_singleton_self _) _ (k 12 (by decide))

theorem xor4Mem_bytes (m : Mem) {c p q : Addr} (hp : Sep4 c p) (hq : Sep4 c q) :
    Spec.Aes.bytesAt (xor4Mem m c p q) c 16 =
      Spec.Cmac.xor (Spec.Aes.bytesAt m p 16) (Spec.Aes.bytesAt m q 16) := by
  rw [xor4Mem_eq m hp hq, bytesAt_store4, xor_words4]

/-- The memory after zeroing the block at `c`, a word at a time. -/
def zero4 (m : Mem) (c : Addr) : Mem := store4 m c 0 0 0 0

theorem zero4_bytes (m : Mem) (c : Addr) : Spec.Aes.bytesAt (zero4 m c) c 16 = Spec.Cmac.zeros 16 := by
  rw [zero4, bytesAt_store4, le4_zero]; decide

/-- The memory after forming a counter block: the block at `c` is the block
at `p` XORed with the block at `q`, and the block at `p` is zeroed. -/
def chainMem4 (m : Mem) (c p q : Addr) : Mem := zero4 (xor4Mem m c p q) p

theorem chainMem4_frame (m : Mem) (C P Q : Addr) : Frame [⟨C, 16⟩, ⟨P, 16⟩] m (chainMem4 m C P Q) :=
  ((xor4Mem_frame m C P Q).mono (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])).trans
    ((frame_store4 P 0 0 0 0).mono (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]))

theorem chainMem4_state (m : Mem) (C P Q : Addr) :
    Spec.Aes.bytesAt (chainMem4 m C P Q) P 16 = Spec.Cmac.zeros 16 := zero4_bytes _ _

theorem chainMem4_counter (m : Mem) {C P Q : Addr} (hcp : (⟨C, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hcq : (⟨C, 16⟩ : Region).Disjoint ⟨Q, 16⟩) :
    Spec.Aes.bytesAt (chainMem4 m C P Q) C 16 =
      Spec.Cmac.xor (Spec.Aes.bytesAt m P 16) (Spec.Aes.bytesAt m Q 16) := by
  rw [chainMem4, zero4, bytesAt_frame16 (frame_store4 P 0 0 0 0) (by simpa using hcp),
    xor4Mem_bytes m (Sep4.of_disjoint hcp) (Sep4.of_disjoint hcq)]

end VG.Proof.Cmac
