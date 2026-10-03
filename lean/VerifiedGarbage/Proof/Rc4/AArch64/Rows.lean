import VerifiedGarbage.Proof.Rc4.AArch64.Group

/-!
# The table in memory, rotated

`loadTable_ok` loads row `(B + 16 r) mod 256` of the table at `x0` into
table register `r`, for a base `B` (in `x8`) that is a multiple of 16, so
that the registers hold the table from `B` (`TableIn`); `storeTable_ok`
stores the registers back the same way.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem and255 (x : BitVec 64) : x &&& 255#64 = BitVec.ofNat 64 (x.toNat % 256) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (255#64).toNat = 2 ^ 8 - 1 := rfl
  rw [BitVec.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- The row address of table register `r`, for the base `B`. -/
def rowOff (B r : Nat) : Nat := (B + 16 * r) % 256

theorem hand (B r : Nat) : (BitVec.ofNat 64 B + BitVec.ofNat 64 (16 * r)) &&& 255#64 =
    BitVec.ofNat 64 (rowOff B r) := by
  rw [and255, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, rowOff]
  congr 1; omega

theorem rowOff_le {B : Nat} (r : Nat) (hB : B % 16 = 0) : rowOff B r + 16 ≤ 256 := by
  simp only [rowOff]; omega

theorem rowLoad_ok {s : State} {B r : Nat} (hr : r < 16) (hB : B % 16 = 0)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 B) (h9 : s.gpr .x9 = 255#64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .x0) 256) :
    WP isa (.block (rowAddr r ++ ([.ldrq (treg r) .x7 0] : List Instr))) s fun t =>
      t.v (treg r) = s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (rowOff B r)) 16 ∧
      (∀ v, v ≠ treg r → t.v v = s.v v) ∧ (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hrow := region_offset _ _ _ (rowOff B r) 16 (by simp only [rowOff]; omega)
    (rowOff_le r hB) hp
  unfold rowAddr
  have himm : 16 * r < 4096 := by omega
  rrun [List.cons_append, List.nil_append, himm, h8, h9, hand, hrow]
  exact ⟨fun v hv => by simp [hv], fun g h6 h7 => by simp [h6, h7], rfl⟩

def loadN (n : Nat) : List Instr := (List.range n).flatMap fun r => rowAddr r ++ [.ldrq (treg r) .x7 0]

theorem loadN_succ (n : Nat) :
    loadN (n + 1) = loadN n ++ (rowAddr n ++ ([.ldrq (treg n) .x7 0] : List Instr)) := by
  simp only [loadN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem loadN_ok {s : State} {B : Nat} (hB : B % 16 = 0) (h8 : s.gpr .x8 = BitVec.ofNat 64 B)
    (h9 : s.gpr .x9 = 255#64) (hp : InRegions (s.rd ++ s.wr) (s.gpr .x0) 256) {n : Nat} (hn : n ≤ 16) :
    WP isa (.block (loadN n)) s fun t =>
      (∀ r < n, t.v (treg r) = s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (rowOff B r)) 16) ∧
      (∀ v, (∀ r < 16, v ≠ treg r) → t.v v = s.v v) ∧ (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨fun r h => absurd h (by omega), fun _ _ => rfl, fun _ _ _ => rfl,
      rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [loadN_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨rows, vk, gk, m, rd, wr, sp⟩ => ?_
    have t8 : t.gpr .x8 = BitVec.ofNat 64 B := by rw [gk _ (by decide) (by decide), h8]
    have t9 : t.gpr .x9 = 255#64 := by rw [gk _ (by decide) (by decide), h9]
    have t0 : t.gpr .x0 = s.gpr .x0 := gk _ (by decide) (by decide)
    have tp : InRegions (t.rd ++ t.wr) (t.gpr .x0) 256 := by rw [rd, wr, t0]; exact hp
    refine WP.mono (rowLoad_ok (s := t) (B := B) (r := n) (by omega) hB t8 t9 tp)
      fun u ⟨row, uv, ug, um, urd, uwr, usp⟩ => ?_
    refine ⟨fun r hr => ?_, fun v hv => by rw [uv v (hv n (by omega)), vk v hv],
      fun g a b => by rw [ug g a b, gk g a b], by rw [um, m], by rw [urd, rd], by rw [uwr, wr],
      by rw [usp, sp]⟩
    by_cases hrn : r = n
    · subst hrn; rw [row, m, t0]
    · rw [uv _ (fun e => hrn (treg_inj _ (by omega) _ (by omega) e)), rows r (by omega)]

theorem loadTable_eq : loadTable = loadN 16 := rfl

/-- Byte `e` of a 16-byte load. -/
theorem vbyte_read (m : Mem) (a : Addr) {e : Nat} (he : e < 16) :
    vbyte (m.read a 16) e = m (a + BitVec.ofNat 64 e) := Mem.extractLsb'_read m a he

theorem rows_table {s : State} {m : Mem} {p : Addr} {B : Nat} (hB : B % 16 = 0)
    (h : ∀ r < 16, s.v (treg r) = m.read (p + BitVec.ofNat 64 (rowOff B r)) 16) :
    TableIn s B (contextAt m p).table := by
  intro k hk
  have hidx : rowOff B (k / 16) + k % 16 = (BitVec.ofNat 8 (B + k)).toNat := by
    simp only [rowOff, BitVec.toNat_ofNat]; omega
  rw [table_get, tbyte, h _ (by omega), vbyte_read _ _ (by omega), BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, hidx]

/-! ## Storing the table -/

theorem rowStore_ok {s : State} {B r : Nat} (hr : r < 16) (hB : B % 16 = 0)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 B) (h9 : s.gpr .x9 = 255#64)
    (hp : InRegions s.wr (s.gpr .x0) 256) :
    WP isa (.block (rowAddr r ++ ([.strq (treg r) .x7 0] : List Instr))) s fun t =>
      t.mem = s.mem.write (s.gpr .x0 + BitVec.ofNat 64 (rowOff B r)) 16 (s.v (treg r)) ∧
      t.v = s.v ∧ (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hrow := region_offset _ _ _ (rowOff B r) 16 (by simp only [rowOff]; omega)
    (rowOff_le r hB) hp
  have himm : 16 * r < 4096 := by omega
  unfold rowAddr
  rrun [List.cons_append, List.nil_append, himm, h8, h9, hand, hrow, State.store]
  exact ⟨fun g h6 h7 => by simp [h6, h7], rfl⟩

def storeN (n : Nat) : List Instr := (List.range n).flatMap fun r => rowAddr r ++ [.strq (treg r) .x7 0]

theorem storeN_succ (n : Nat) :
    storeN (n + 1) = storeN n ++ (rowAddr n ++ ([.strq (treg n) .x7 0] : List Instr)) := by
  simp only [storeN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem storeTable_eq : storeTable = storeN 16 := rfl

/-- Rows `r` and `n` of the table do not overlap. -/
theorem row_apart {p : Addr} {B r n e : Nat} (hB : B % 16 = 0) (hr : r < 16) (hn : n < 16)
    (hrn : r ≠ n) (he : e < 16) :
    ¬ (p + BitVec.ofNat 64 (rowOff B r + e) - (p + BitVec.ofNat 64 (rowOff B n))).toNat < 16 := by
  rw [Offset.add_sub_add_left, Offset.toNat_sub_ofNat, BitVec.toNat_ofNat]
  simp only [rowOff]
  omega

theorem storeN_ok {s : State} {B : Nat} (hB : B % 16 = 0) (h8 : s.gpr .x8 = BitVec.ofNat 64 B)
    (h9 : s.gpr .x9 = 255#64) (hp : InRegions s.wr (s.gpr .x0) 256) {n : Nat} (hn : n ≤ 16) :
    WP isa (.block (storeN n)) s fun t =>
      (∀ r < n, ∀ e < 16, t.mem (s.gpr .x0 + BitVec.ofNat 64 (rowOff B r + e)) =
        vbyte (s.v (treg r)) e) ∧
      (∀ y, (∀ r < n, ¬ (y - (s.gpr .x0 + BitVec.ofNat 64 (rowOff B r))).toNat < 16) →
        t.mem y = s.mem y) ∧
      t.v = s.v ∧ (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨fun r h => absurd h (by omega), fun _ _ => rfl, rfl,
      fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [storeN_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨rows, fr, tv, gk, rd, wr, sp⟩ => ?_
    have t8 : t.gpr .x8 = BitVec.ofNat 64 B := by rw [gk _ (by decide) (by decide), h8]
    have t9 : t.gpr .x9 = 255#64 := by rw [gk _ (by decide) (by decide), h9]
    have t0 : t.gpr .x0 = s.gpr .x0 := gk _ (by decide) (by decide)
    have tp : InRegions t.wr (t.gpr .x0) 256 := by rw [wr, t0]; exact hp
    refine WP.mono (rowStore_ok (s := t) (B := B) (r := n) (by omega) hB t8 t9 tp)
      fun u ⟨um, uv, ug, urd, uwr, usp⟩ => ?_
    refine ⟨fun r hr e he => ?_, fun y hy => ?_, by rw [uv, tv], fun g a b => by rw [ug g a b, gk g a b],
      by rw [urd, rd], by rw [uwr, wr], by rw [usp, sp]⟩
    · rw [um, t0, Mem.write]
      by_cases hrn : r = n
      · subst hrn
        have d : (s.gpr .x0 + BitVec.ofNat 64 (rowOff B r + e) -
            (s.gpr .x0 + BitVec.ofNat 64 (rowOff B r))).toNat = e := by
          rw [Offset.add_sub_add_left, Offset.toNat_sub_ofNat]
          simp only [rowOff, BitVec.toNat_ofNat]
          omega
        rw [d, ite_eq_left he, tv]
        rfl
      · rw [ite_eq_right (row_apart hB (by omega) (by omega) hrn he), rows r (by omega) e he]
    · rw [um, t0, Mem.write, ite_eq_right (hy n (by omega)), fr y fun r hr => hy r (by omega)]

/-- The rows stored are the table from `B`. -/
theorem stored_table {s : State} {m : Mem} {p : Addr} {B : Nat} (hB : B % 16 = 0) {T : Table}
    (hT : TableIn s B T)
    (h : ∀ r < 16, ∀ e < 16, m (p + BitVec.ofNat 64 (rowOff B r + e)) = vbyte (s.v (treg r)) e) :
    (contextAt m p).table = T := by
  apply Vector.ext
  intro k hk
  have hx := (BitVec.ofNat 8 k).isLt
  let r := (k + 256 - B % 256) % 256 / 16
  have hr : r < 16 := by omega
  have hrow : rowOff B r + k % 16 = k := by simp only [rowOff, r]; omega
  have e1 : (contextAt m p).table[k] = m (p + BitVec.ofNat 64 k) := by
    simp only [contextAt, Vector.getElem_ofFn]
  have e2 : m (p + BitVec.ofNat 64 k) = vbyte (s.v (treg r)) (k % 16) := by
    rw [← h r hr _ (by omega), hrow]
  rw [e1, e2]
  have := hT (16 * r + k % 16) (by omega)
  simp only [tbyte, show (16 * r + k % 16) / 16 = r by omega, show (16 * r + k % 16) % 16 = k % 16 by omega] at this
  have hk' : (BitVec.ofNat 8 (B + (16 * r + k % 16))).toNat = k := by
    simp only [BitVec.toNat_ofNat, r]; omega
  rw [this, hk']
  simp [Vector.getD, Array.getD, hk]

end VG.Proof.Rc4.AArch64
