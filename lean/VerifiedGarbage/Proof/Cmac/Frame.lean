import VerifiedGarbage.Proof.Cmac.Mem

/-!
# CMAC: blocks in memory under frames

Untrusted: everything here is checked by Lean.

What the implementations' stores of 64-bit words leave in memory, on any
target: the bytes outside a frame are unchanged (`bytesAt_frame`), and the
memory after forming a counter block `C = P ⊕ Q` and zeroing `P`
(`chainMem`), as each block of `update` does.
-/

namespace VG.Proof.Cmac

open VG

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m p n := by
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem bytesAt_frame16 {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : Spec.Aes.bytesAt m' p 16 = Spec.Aes.bytesAt m p 16 :=
  bytesAt_frame hf hd (by decide)

theorem frame_store2 {m : Mem} (p : Addr) (w₀ w₁ : BitVec 64) :
    Frame [⟨p, 16⟩] m ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base p (d := 0) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base p (d := 8) (n := 8) (k := 16) (by decide) (by decide))

theorem readW_frame16 {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {d : Nat} (hd8 : d + 8 ≤ 16)
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨p + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base p hd8)) (by decide)

/-- The memory after forming a counter block: the block at `c` is the block
at `p` XORed with the block at `q`, and the block at `p` is zeroed. -/
def chainMem (m : Mem) (c p q : Addr) : Mem :=
  let m₁ := m.writeW c (m.readW p 64 ^^^ m.readW q 64)
  let m₂ := m₁.writeW (c + BitVec.ofNat 64 8) (m₁.readW (p + BitVec.ofNat 64 8) 64 ^^^ m₁.readW (q + BitVec.ofNat 64 8) 64)
  (m₂.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)

theorem chainMem_frame (m : Mem) (C P Q : Addr) : Frame [⟨C, 16⟩, ⟨P, 16⟩] m (chainMem m C P Q) := by
  have f₁ : Frame [⟨C, 16⟩, ⟨P, 16⟩] m _ :=
    (frame_store2 (m := m) C (m.readW P 64 ^^^ m.readW Q 64)
      ((m.writeW C (m.readW P 64 ^^^ m.readW Q 64)).readW (P + BitVec.ofNat 64 8) 64 ^^^
        (m.writeW C (m.readW P 64 ^^^ m.readW Q 64)).readW (Q + BitVec.ofNat 64 8) 64)).mono
      (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  exact f₁.trans ((frame_store2 P 0 0).mono (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]))

theorem chainMem_state (m : Mem) (C P Q : Addr) :
    Spec.Aes.bytesAt (chainMem m C P Q) P 16 = Spec.Cmac.zeros 16 := by
  rw [chainMem, bytesAt_store2, le8_zero]; rfl

theorem chainMem_counter (m : Mem) {C P Q : Addr} (hcp : (⟨C, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hcq : (⟨C, 16⟩ : Region).Disjoint ⟨Q, 16⟩) :
    Spec.Aes.bytesAt (chainMem m C P Q) C 16 =
      Spec.Cmac.xor (Spec.Aes.bytesAt m P 16) (Spec.Aes.bytesAt m Q 16) := by
  rw [chainMem, bytesAt_frame16 (frame_store2 P 0 0) (by simpa using hcp), bytesAt_store2]
  have g : Frame [⟨C, 16⟩] m (m.writeW C (m.readW P 64 ^^^ m.readW Q 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by simpa using Offset.contains_base C (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  rw [readW_frame16 g (d := 8) (by decide) (by simpa using hcp.symm),
    readW_frame16 g (d := 8) (by decide) (by simpa using hcq.symm)]
  exact xor_words m P Q

end VG.Proof.Cmac
