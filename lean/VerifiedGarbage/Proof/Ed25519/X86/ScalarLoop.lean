import VerifiedGarbage.Proof.Ed25519.X86.ScalarBody

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Spec.Ed25519 (L decodeLE)

def scalarInput (m : Mem) (x : BitVec 32) : List Byte :=
  (List.range 64).map fun i => m (addr x (128 + i))

theorem scalarInput_length (m : Mem) (x : BitVec 32) : (scalarInput m x).length = 64 := by
  simp only [scalarInput, List.length_map, List.length_range]

theorem scalar_suffix (m : Mem) (x : BitVec 32) {n : Nat} (hn : n < 64) :
    decodeLE ((scalarInput m x).drop n) % L =
      (256 * (decodeLE ((scalarInput m x).drop (n + 1)) % L) + (m (addr x (128 + n))).toNat) % L := by
  rw [List.drop_eq_getElem_cons (by rw [scalarInput_length]; exact hn), reduce_cons]
  simp only [scalarInput, List.getElem_map, List.getElem_range]

theorem scalarInput_byte {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (hf : Frame (scalarBodyFrame x) m m') {n : Nat} (hn : n < 64) :
    m' (addr x (128 + n)) = m (addr x (128 + n)) := by
  apply hf
  intro r hr
  simp only [scalarBodyFrame, scalarFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hb : (sub x (128 + n) 1).Contains (addr x (128 + n)) 1 := Region.contains_self _ _
  rcases hr with rfl | rfl | rfl
  · exact (sub_disj (by omega_using [hx, hn]) (by omega_using [hx])
      (Or.inr (by omega_using []))) _ hb
  · exact (sub_disj (by omega_using [hx, hn]) (by simp only [scalarR]; omega_using [hx])
      (Or.inr (by simp only [scalarR]; omega_using []))) _ hb
  · exact (sub_disj (by omega_using [hx, hn]) (by simp only [T]; omega_using [hx])
      (Or.inl (by simp only [T]; omega_using [hn]))) _ hb

structure ScalarInv (x : BitVec 32) (s₀ : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 64
  counter : s.gpr .esi = BitVec.ofNat 32 n
  value : fe s.mem x scalarR = decodeLE ((scalarInput s₀.mem x).drop n) % L
  keeps : ScalarKeep s₀ s
  frame : Frame (scalarBodyFrame x) s₀.mem s.mem

theorem scalarLoop_ok {x : BitVec 32} {s₀ : State} (hc : Ctx x s₀)
    (hs : s₀.gpr .esi = 64) (hz : fe s₀.mem x scalarR = 0) :
    WP isa (.loop (.block scalarByte) .ne) s₀ fun t => ScalarKeep s₀ t ∧
      Frame (scalarBodyFrame x) s₀.mem t.mem ∧ fe t.mem x scalarR = decodeLE (scalarInput s₀.mem x) % L := by
  apply WP.loop (ScalarInv x s₀) (n := 64)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega_using [this] : n ≠ 0)
    have hk : k < 64 := by have := hi.bound; omega_using [this]
    refine WP.mono (scalarByte_ok (hi.keeps.ctx hc) hk hi.counter
      (by rw [hi.value]; exact Nat.mod_lt _ order_pos)) fun t ⟨kt, st, zt, ft, vt⟩ => ?_
    have v : fe t.mem x scalarR = decodeLE ((scalarInput s₀.mem x).drop k) % L := by
      rw [vt, hi.value, scalarInput_byte hc.fit hi.frame hk, scalar_suffix _ _ hk]
    have keep := hi.keeps.trans kt
    have frame := hi.frame.trans ft
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, zt, decide_true, Option.map_some, Bool.not_true],
        keep, frame, by simpa only [List.drop_zero] using v⟩
    · exact Or.inr ⟨by simp only [eval, zt, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega_using [], ⟨by omega_using [hk0], by omega_using [hk], st, v, keep, frame⟩⟩
  · refine ⟨by decide, by decide, hs, ?_, ScalarKeep.refl _, Frame.refl _ _⟩
    rw [hz, List.drop_eq_nil_of_le (by rw [scalarInput_length])]
    rfl
end VG.Proof.Ed25519.X86
