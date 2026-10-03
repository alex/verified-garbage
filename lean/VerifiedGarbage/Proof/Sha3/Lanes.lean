import VerifiedGarbage.Proof.Sha3.Spec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Keccak-f[1600]: states in memory, for every target

The lanes of a state stored as `[u64; 25]`, where a round of the
implementations reads and writes (`Env`), the state a round computes
(`outState`), and offsets from a pointer, none of which depend on the target.
-/

namespace VG.Proof.Sha3

open VG.Spec.Sha3 (Lane rnd RC)

/-! ## Offsets -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

/-- Two runs of bytes at offsets of the same base. -/
theorem off_disjoint (p : Addr) {a n b k : Nat} (ha : a + n ≤ 2 ^ 32) (hb : b + k ≤ 2 ^ 32)
    (h : a + n ≤ b ∨ b + k ≤ a) :
    Region.Disjoint ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p + BitVec.ofNat 64 b, k⟩ := Offset.disjoint p h (by omega) (by omega)

theorem off_sub (p : Addr) {a n b k : Nat} (_hb : b + k ≤ 2 ^ 32) (h₁ : b ≤ a) (h₂ : a + n ≤ b + k) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p + BitVec.ofNat 64 b, k⟩ := Offset.sub p h₁ h₂

theorem add_zero' (p : Addr) : p + BitVec.ofNat 64 0 = p := by simp

theorem sub_prefix' {base : Addr} {len len' : Nat} (h : len ≤ len') :
    Region.Sub ⟨base, len⟩ ⟨base, len'⟩ := Region.sub_prefix h

/-! ## Lanes -/

/-- Lane `i` of the state at `p`. -/
abbrev laneAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (8 * i)

/-- The state at `p` holds `A`. -/
def Lanes (m : Mem) (p : Addr) (A : Spec.Sha3.State) : Prop :=
  ∀ i (hi : i < 25), m.readW (laneAddr p i) 64 = A[i]

theorem lane_contains (p : Addr) {i : Nat} (hi : i < 25) : (⟨p, 200⟩ : Region).Contains (laneAddr p i) 8 := by
  simp only [Region.Contains, laneAddr]
  rw [show p + BitVec.ofNat 64 (8 * i) - p = BitVec.ofNat 64 (8 * i) by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem lane_sep (p : Addr) {i j : Nat} (hi : i < 25) (hj : j < 25) (h : i ≠ j) :
    Mem.Sep (laneAddr p i) 8 (laneAddr p j) 8 := by
  intro x hx hy
  simp only [laneAddr] at hx hy
  bv_omega

/-- Where a round reads and writes: the state at `src`, the round constant
at `rcp`, and the state at `dst`, which overlaps neither. -/
structure Env (rd wr : List Region) (src dst rcp : Addr) : Prop where
  src_in : ∀ i < 25, InRegions (rd ++ wr) (laneAddr src i) 8
  dst_out : ∀ i < 25, InRegions wr (laneAddr dst i) 8
  rc_in : InRegions (rd ++ wr) rcp 8
  dst_src : Region.Disjoint ⟨dst, 200⟩ ⟨src, 200⟩
  dst_rc : Region.Disjoint ⟨dst, 200⟩ ⟨rcp, 8⟩

/-- Writing the state at `dst` keeps the lanes at `src`. -/
theorem Env.src_frame {rd wr : List Region} {src dst rcp : Addr} (h : Env rd wr src dst rcp)
    {m m' : Mem} (hf : Frame [⟨dst, 200⟩] m m') {i : Nat} (hi : i < 25) :
    m'.readW (laneAddr src i) 64 = m.readW (laneAddr src i) 64 :=
  hf.readW (lane_contains src hi) (by simpa using h.dst_src.symm) (by decide)

theorem Env.rc_frame {rd wr : List Region} {src dst rcp : Addr} (h : Env rd wr src dst rcp)
    {m m' : Mem} (hf : Frame [⟨dst, 200⟩] m m') : m'.readW rcp 64 = m.readW rcp 64 :=
  hf.readW (Region.contains_self _ _) (by simpa using h.dst_rc.symm) (by decide)

/-! ## The round -/

/-- The round's output. -/
def outState (A : Spec.Sha3.State) (rc : Lane) : Spec.Sha3.State :=
  Vector.ofFn fun i => out A rc (i.val % 5) (i.val / 5)

theorem outState_eq (A : Spec.Sha3.State) (ir : Nat) : outState A (RC ir) = rnd A ir := by
  apply Vector.ext
  intro i hi
  simp only [outState, Vector.getElem_ofFn]
  have := rnd_get A ir (x := i % 5) (y := i / 5) (Nat.mod_lt _ (by omega)) (by omega)
  simp only [show i % 5 + 5 * (i / 5) = i by omega] at this
  exact this.symm

theorem foldl_succ (A : Spec.Sha3.State) (r : Nat) :
    (List.range (r + 1)).foldl rnd A = rnd ((List.range r).foldl rnd A) r := by
  simp [List.range_succ, List.foldl_append]

end VG.Proof.Sha3
