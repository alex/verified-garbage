import VerifiedGarbage.Proof.TripleDes.Bitslice.Io
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Bytes

/-!
# Three bitsliced DES passes, and the blocks they come from

Target-independent facts for bitsliced TDEA on `w`-bit words: the state
words a round, pairs of rounds and a pass compute depend only on the 64
state words (`*_congr`); TDEA's three passes (`tdeaW`) do in every lane
what TDEA does between IP and FP (`tdeaW_lane`); and ECB's result is that
of each of its blocks (`ecb_blocks`).
-/

namespace VG.Proof.TripleDes.Bitslice

open VG VG.Spec.TripleDes VG.Impl.TripleDes.Bitslice VG.Proof.TripleDes

variable {w : Nat}

theorem roundW_congr (ρ : Role) (k : BitVec 48) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) : ∀ x < 64, roundW ρ k W x = roundW ρ k W' x :=
  steps_congr ρ k (Nat.le_refl 8) hW

theorem pairs_congr (key : Nat → BitVec 48) (n : Nat) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) : ∀ x < 64, pairs key n W x = pairs key n W' x := by
  induction n with
  | zero => exact hW
  | succ n ih =>
    intro x hx
    simp only [pairs]
    exact roundW_congr .ab _ (roundW_congr .ba _ ih) x hx

theorem pairs_keys_congr {key key' : Nat → BitVec 48} (n : Nat)
    (hk : ∀ r < 2 * n, key r = key' r) (W : Nat → BitVec w) : pairs key n W = pairs key' n W := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pairs]
    rw [ih (fun r hr => hk r (by omega)), hk (2 * n) (by omega), hk (2 * n + 1) (by omega)]

theorem partner_lt : ∀ k < 128, ∀ y, partner k = some y → y < 64 := by
  intro k hk y h
  have key : ∀ k < 128, (partner k).all (· < 64) = true := by decide +kernel
  have := key k hk
  rw [h] at this
  simpa using this

theorem swapW_congr {W W' : Nat → BitVec w} (hW : ∀ y < 64, W y = W' y) :
    ∀ x < 64, swapW W x = swapW W' x := by
  intro x hx
  simp only [swapW]
  rcases hp : partner x with _ | y
  · exact hW x hx
  · exact hW y (partner_lt x (by omega) y hp)

theorem passW_congr (keys : DesSchedule) (d : Direction) {W W' : Nat → BitVec w}
    (hW : ∀ y < 64, W y = W' y) : ∀ x < 64, passW keys d W x = passW keys d W' x :=
  swapW_congr (pairs_congr _ 8 hW)

theorem ipLane_congr {W W' : Nat → BitVec w} (hW : ∀ x < 64, W x = W' x) (b : Nat) :
    ipLane W b = ipLane W' b := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [ipLane_bit _ _ ht, ipLane_bit _ _ ht, hW _ (ipWord_lt t ht)]

/-! ## TDEA -/

/-- TDEA's three passes with the schedule `K`, in the direction `d`. -/
def tdeaW (K : Schedule) : Direction → (Nat → BitVec w) → Nat → BitVec w
  | .encrypt, W => passW (componentSchedule K 2) .encrypt
      (passW (componentSchedule K 1) .decrypt (passW (componentSchedule K 0) .encrypt W))
  | .decrypt, W => passW (componentSchedule K 0) .decrypt
      (passW (componentSchedule K 1) .encrypt (passW (componentSchedule K 2) .decrypt W))

/-- What ECB does to one block. -/
def blockOut (K : Schedule) : Direction → Block → Block
  | .encrypt => encryptBlock K
  | .decrypt => decryptBlock K

/-- The three DES cores of TDEA, between IP and FP. -/
def cores (K : Schedule) : Direction → BitVec 64 → BitVec 64
  | .encrypt, x => desCore (componentSchedule K 2) .encrypt
      (desCore (componentSchedule K 1) .decrypt (desCore (componentSchedule K 0) .encrypt x))
  | .decrypt, x => desCore (componentSchedule K 0) .decrypt
      (desCore (componentSchedule K 1) .encrypt (desCore (componentSchedule K 2) .decrypt x))

theorem tdeaW_lane (K : Schedule) (d : Direction) (W : Nat → BitVec w) {b : Nat} (hb : b < w) :
    ipLane (tdeaW K d W) b = cores K d (ipLane W b) := by
  cases d <;> simp only [tdeaW, cores, pass_lane _ _ _ hb]

theorem blockOut_cores (K : Schedule) (d : Direction) (B : Block) :
    blockOut K d B = encodeBlock (permute fp (cores K d (permute ip (decodeBlock B)))) := by
  cases d
  · exact encryptBlock_eq_cores K B
  · exact decryptBlock_eq_cores K B

/-! ## Blocks in memory -/

/-- Block `i` of the data at `p`. -/
abbrev wAt (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (8 * i)

theorem wAt_wAt (D : Addr) (a i : Nat) : wAt (wAt D a) i = wAt D (a + i) := by
  simp only [wAt, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2; omega

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

theorem toNat_ofNat_of_le {m n : Nat} (hm : m ≤ n) (hn : 8 * n ≤ 2 ^ 64) :
    (BitVec.ofNat 64 m).toNat = m := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem ecb_blocks (K : Schedule) (d : Direction) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, blockAt m' (wAt D b) = blockOut K d (blockAt m (wAt D b))) :
    blocksAt m' D n = Spec.TripleDes.ecb K d (blocksAt m D n) := by
  simp only [blocksAt, Spec.TripleDes.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  exact h b (List.mem_range.mp hb)

end VG.Proof.TripleDes.Bitslice
