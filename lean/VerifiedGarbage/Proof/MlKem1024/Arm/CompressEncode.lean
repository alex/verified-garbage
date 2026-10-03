import VerifiedGarbage.Proof.MlKem.Arm.CompressEncode
import VerifiedGarbage.Proof.MlKem.Encode1024
import VerifiedGarbage.Impl.MlKem1024.Arm.Poly
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on 32-bit ARM: `vg_mlkem1024_compress_encode`

A loop for each width `d ∈ {5, 11}` over the 32 groups of 8 coefficients,
whose body is the 8 fields of a group, each run once for any field
(`field_step`) from the steps of its code: the coefficient compressed
(`coeff5_ok`, `coeff11_ok`), its low bits added to (or stored in) its first
byte (`head0_ok`, `headT_ok`), and each next byte stored (`next_ok`).

The bytes of the group written so far are those of the number `acc` of
its first fields (`GB`, `acc`): `acc` of the first `k` fields is less than
`2^(d k)`, and adding field `k` at bit `d k = 8 j + t` changes no byte
before `j` (`add_bytes_lo`), adds the field shifted by `t` to byte `j`
(`add_byte_j`), and makes byte `j + m` the field shifted down by `8 m - t`
(`add_bytes_hi`). After the 8 fields, `acc` is the number of the group of
`compressEncode5_group` or `compressEncode11_group`.
-/

namespace VG.Proof.MlKem1024.Arm.CompressEncode

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)
open VG.Proof.MlKem.Arm.CompressEncode (addB addB_toNat byte_eq)

/-! ## The values -/

/-- `(x · M + 2¹⁸ - 2⁸) >> 19`, as `compressAt4` computes it. -/
def cmpV4 (M x : BitVec 32) : BitVec 32 := (x * M + 0x40000 - 0x100) >>> 19

/-- The multipliers, as `movw` (and `movt`) build them. -/
def m5 : BitVec 32 := (5040 : BitVec 16).setWidth 32
def m11 : BitVec 32 := (0x4 : BitVec 16) ++ ((0xEBEE : BitVec 16).setWidth 32).extractLsb' 0 16

theorem m5_toNat : m5.toNat = compressMul1024 5 := by decide
theorem m11_toNat : m11.toNat = compressMul1024 11 := by decide

theorem mem_widths {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) : d = 5 ∨ d = 11 :=
  mem_compressWidths1024 hd

theorem cmpV4_toNat {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) {M : BitVec 32}
    (hM : M.toNat = compressMul1024 d) (x : Zq) :
    (cmpV4 M (BitVec.ofNat 32 x.val)).toNat = (x.val * compressMul1024 d + compressAdd1024) / 2 ^ 19 := by
  have hx := val_lt x
  have ha := compress1024_arg_lt hd x
  have hp : (BitVec.ofNat 32 x.val * M).toNat = x.val * compressMul1024 d := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, hM, Nat.mod_eq_of_lt (a := x.val) (by omega)]
    exact Nat.mod_eq_of_lt (by unfold compressAdd1024 at ha; omega)
  unfold compressAdd1024 at ha ⊢
  unfold cmpV4
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  refine congrArg (· / 2 ^ 19) ?_
  have e1 : (0x40000 : BitVec 32).toNat = 262144 := rfl
  have e2 : (0x100 : BitVec 32).toNat = 256 := rfl
  rw [BitVec.toNat_sub, BitVec.toNat_add, hp, e1, e2]
  omega

/-- `Compress₅` of a coefficient, as `ceCoeff 5` computes it. -/
theorem c5_eq (x : Zq) :
    cmpV4 m5 (BitVec.ofNat 32 x.val) &&& 31 = BitVec.ofNat 32 (compress 5 x) := by
  apply BitVec.eq_of_toNat_eq
  have e31 : (31 : BitVec 32).toNat = 2 ^ 5 - 1 := rfl
  rw [BitVec.toNat_and, cmpV4_toNat (d := 5) (by decide) m5_toNat, e31, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, compress1024_eq (d := 5) (by decide)]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm

/-- `Compress₁₁` of a coefficient, as `ceCoeff 11` computes it. -/
theorem c11_eq (x : Zq) : cmpV4 m11 (BitVec.ofNat 32 x.val) = BitVec.ofNat 32 (compress 11 x) := by
  apply BitVec.eq_of_toNat_eq
  rw [cmpV4_toNat (d := 11) (by decide) m11_toNat, compress11_eq, BitVec.toNat_ofNat]
  have := val_lt x
  exact (Nat.mod_eq_of_lt (by show (x.val * 322542 + 261888) / 2 ^ 19 < 2 ^ 32; omega)).symm

/-! ## The number of the fields written -/

/-- Adding field `c` at bit `8 j + t` to a number `A < 2^(8 j + t)`: bytes
from `j` on. -/
theorem add_div {A c j t : Nat} :
    (A + c * 2 ^ (8 * j + t)) / 2 ^ (8 * j) = A / 2 ^ (8 * j) + c * 2 ^ t := by
  rw [show c * 2 ^ (8 * j + t) = c * 2 ^ t * 2 ^ (8 * j) by rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm (2 ^ t)],
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]

/-- Bytes before `j` do not change. -/
theorem add_bytes_lo {A c j t b : Nat} (hb : b < j) :
    (A + c * 2 ^ (8 * j + t)) / 2 ^ (8 * b) % 256 = A / 2 ^ (8 * b) % 256 := by
  have e : c * 2 ^ (8 * j + t) = c * 2 ^ (8 * (j - b - 1) + t) * 256 * 2 ^ (8 * b) := by
    rw [show 8 * j + t = 8 * (j - b - 1) + t + 8 + 8 * b by omega, Nat.pow_add, Nat.pow_add,
      show (2 : Nat) ^ 8 = 256 from rfl]
    simp only [Nat.mul_assoc]
  rw [e, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_right]

/-- Byte `j` gets the field shifted by `t`. -/
theorem add_byte_j {A c j t : Nat} :
    (A + c * 2 ^ (8 * j + t)) / 2 ^ (8 * j) % 256 = (A / 2 ^ (8 * j) + c * 2 ^ t) % 256 := by
  rw [add_div]

/-- Byte `j + m` (`m ≥ 1`) is the field shifted down by `8 m - t`. -/
theorem add_bytes_hi {A c j t m : Nat} (hA : A < 2 ^ (8 * j + t)) (ht : t < 8) (hm : 1 ≤ m) :
    (A + c * 2 ^ (8 * j + t)) / 2 ^ (8 * (j + m)) = c / 2 ^ (8 * m - t) := by
  have h1 : A / 2 ^ (8 * j) < 2 ^ t := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm]; exact hA
  have e1 : (A + c * 2 ^ (8 * j + t)) / 2 ^ (8 * (j + m)) =
      (A + c * 2 ^ (8 * j + t)) / 2 ^ (8 * j) / 2 ^ t / 2 ^ (8 * m - t) := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.pow_add,
      show 8 * j + (t + (8 * m - t)) = 8 * (j + m) by omega]
  rw [e1, add_div, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt h1, Nat.zero_add]

/-- A number of `k` fields of `d` bits. -/
theorem acc_step_lt {A c d k : Nat} (hA : A < 2 ^ (d * k)) (hc : c < 2 ^ d) :
    A + c * 2 ^ (d * k) < 2 ^ (d * (k + 1)) := by
  have : c * 2 ^ (d * k) + 2 ^ (d * k) ≤ 2 ^ d * 2 ^ (d * k) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (d * k))]
  omega

/-! ## The steps of a field -/

/-- What the steps of a field keep, but for the memory. -/
structure Keeps (s s' : State) : Prop where
  r0 : s'.gpr .r0 = s.gpr .r0
  r2 : s'.gpr .r2 = s.gpr .r2
  r3 : s'.gpr .r3 = s.gpr .r3
  pres : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.refl (s : State) : Keeps s s := ⟨rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨h₂.r0.trans h₁.r0, h₂.r2.trans h₁.r2, h₂.r3.trans h₁.r3, fun r hr => (h₂.pres r hr).trans (h₁.pres r hr),
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

section
variable {s : State} {x y : BitVec 32}

theorem coeff5_ok {k : Nat} (hk : 4 * k < 4096) (h0 : s.gpr .r0 = x)
    (i0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * k))) 4) :
    WP isa (.block (ceCoeff 5 k)) s fun s' => Keeps s s' ∧ s'.mem = s.mem ∧
      s'.gpr .r1 = cmpV4 m5 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * k))) 32) &&& 31 := by
  run_block [ceCoeff, compressAt4, cmpV4, m5, h0, i0, hk]
  exact ⟨⟨rfl, rfl, rfl, by simp (config := {decide := true}) [preserved], rfl, rfl, rfl⟩, trivial⟩

theorem coeff11_ok {k : Nat} (hk : 4 * k < 4096) (h0 : s.gpr .r0 = x)
    (i0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * k))) 4) :
    WP isa (.block (ceCoeff 11 k)) s fun s' => Keeps s s' ∧ s'.mem = s.mem ∧
      s'.gpr .r1 = cmpV4 m11 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * k))) 32) := by
  run_block [ceCoeff, compressAt4, cmpV4, m11, h0, i0, hk]
  exact ⟨⟨rfl, rfl, rfl, by simp (config := {decide := true}) [preserved], rfl, rfl, rfl⟩, trivial⟩

theorem head0_ok {j : Nat} (hj : j < 4096) (h2 : s.gpr .r2 = y)
    (o : InRegions s.wr (State.addr (y + BitVec.ofNat 32 j)) 1) :
    WP isa (.block (ceHead j 0)) s fun s' => Keeps s s' ∧ s'.gpr .r1 = s.gpr .r1 ∧
      s'.mem = s.mem.writeW (State.addr (y + BitVec.ofNat 32 j)) ((s.gpr .r1).setWidth 8) := by
  run_block [ceHead, h2, o, hj]
  exact ⟨⟨rfl, rfl, rfl, by simp (config := {decide := true}) [preserved], rfl, rfl, rfl⟩, trivial⟩

theorem headT_ok {j t : Nat} (hj : j < 4096) (ht : 1 ≤ t ∧ t ≤ 31) (h2 : s.gpr .r2 = y)
    (i : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 j)) 1)
    (o : InRegions s.wr (State.addr (y + BitVec.ofNat 32 j)) 1) :
    WP isa (.block (ceHead j t)) s fun s' => Keeps s s' ∧ s'.gpr .r1 = s.gpr .r1 ∧
      s'.mem = s.mem.writeW (State.addr (y + BitVec.ofNat 32 j))
        (addB (s.mem (State.addr (y + BitVec.ofNat 32 j))) (s.gpr .r1 <<< t)) := by
  have h0 : t ≠ 0 := by omega
  unfold ceHead
  simp only [h0, ↓reduceIte]
  run_block [h2, i, o, hj, ht, addB]
  exact ⟨⟨rfl, rfl, rfl, by simp (config := {decide := true}) [preserved], rfl, rfl, rfl⟩, trivial⟩

theorem next_ok {j t i : Nat} (hj : j + 1 + i < 4096)
    (hsh : 1 ≤ (if i = 0 then 8 - t else 8) ∧ (if i = 0 then 8 - t else 8) ≤ 31) (h2 : s.gpr .r2 = y)
    (o : InRegions s.wr (State.addr (y + BitVec.ofNat 32 (j + 1 + i))) 1) :
    WP isa (.block (ceNext j t i)) s fun s' => Keeps s s' ∧
      s'.gpr .r1 = s.gpr .r1 >>> (if i = 0 then 8 - t else 8) ∧
      s'.mem = s.mem.writeW (State.addr (y + BitVec.ofNat 32 (j + 1 + i)))
        ((s.gpr .r1 >>> (if i = 0 then 8 - t else 8)).setWidth 8) := by
  run_block [ceNext, h2, o, hj, hsh]
  exact ⟨⟨rfl, rfl, rfl, by simp (config := {decide := true}) [preserved], rfl, rfl, rfl⟩, trivial⟩

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev pf : BitVec 32 := s₀.gpr .r0
abbrev dd : Nat := (s₀.gpr .r1).toNat
abbrev po : BitVec 32 := s₀.gpr .r2
abbrev len : Nat := (s₀.gpr .r3).toNat
abbrev F : Addr := State.addr (pf s₀)
abbrev O : Addr := State.addr (po s₀)
abbrev outR : Region := ⟨O s₀, len s₀⟩
abbrev fp : Poly := polyAt s₀.mem (F s₀)
abbrev CE : List Byte := compressEncode (dd s₀) (fp s₀)

/-- The compressed coefficient `j`. -/
abbrev cc (j : Nat) : Nat := compress (dd s₀) (fp s₀)[j]!

/-- The number of the first `k` fields of group `i`. -/
def acc (i : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => acc i k + cc s₀ (8 * i + k) * 2 ^ (dd s₀ * k)

/-- The bytes of the output: those of the groups before `i`, then the first
`p` bytes of the number `A`, then what was there. -/
def GB (i A p : Nat) (m : Mem) : Prop :=
  ∀ b < len s₀, m (O s₀ + BitVec.ofNat 64 b) =
    if b < dd s₀ * i then (CE s₀)[b]!
    else if b < dd s₀ * i + p then BitVec.ofNat 8 (A / 2 ^ (8 * (b - dd s₀ * i)))
    else s₀.mem (O s₀ + BitVec.ofNat 64 b)

end

theorem acc_lt (s₀ : State) (i : Nat) : ∀ k, acc s₀ i k < 2 ^ (dd s₀ * k)
  | 0 => by simp [acc]
  | k + 1 => acc_step_lt (acc_lt s₀ i k) (compress_lt _ _)

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (F s₀)]
  wr : s₀.wr = [outR s₀]
  disj : (polyRegion (F s₀)).Disjoint (outR s₀)
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitO : (po s₀).toNat + len s₀ ≤ 2 ^ 32
  d : dd s₀ ∈ Spec.MlKem1024.compressWidths
  len : len s₀ = 32 * dd s₀
  red : Reduced s₀.mem (F s₀)

/-- Within iteration `i` of the loop, after the first `k` fields of the
group, with the bytes `GB i A p`. -/
structure Mid (s₀ : State) (i A p : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pf s₀ + BitVec.ofNat 32 (32 * i)
  r2 : s.gpr .r2 = po s₀ + BitVec.ofNat 32 (dd s₀ * i)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (32 - i))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [outR s₀] s₀.mem s.mem
  bytes : GB s₀ i A p s.mem

theorem Mid.keeps {s₀ : State} {i A p : Nat} {s s' : State} (h : Mid s₀ i A p s) (k : Keeps s s')
    {A' p' : Nat} (hf : Frame [outR s₀] s₀.mem s'.mem) (hb : GB s₀ i A' p' s'.mem) : Mid s₀ i A' p' s' :=
  ⟨k.r0.trans h.r0, k.r2.trans h.r2, k.r3.trans h.r3, k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp,
    fun r hr => (k.pres r hr).trans (h.pres r hr), hf, hb⟩

section
variable {s₀ : State} (hp : Pre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
  (hf : Frame [outR s₀] s₀.mem s.mem)
include hp hrd hwr hf

/-- Coefficient `j = 8 i + k` of the input: its address, that it can be
read, and its value. -/
theorem coeff_at {i k : Nat} (hk : 8 * i + k < 256) :
    State.addr (pf s₀ + BitVec.ofNat 32 (32 * i) + BitVec.ofNat 32 (4 * k)) = coeffAddr (F s₀) (8 * i + k) ∧
    InRegions (s.rd ++ s.wr) (coeffAddr (F s₀) (8 * i + k)) 4 ∧
    s.mem.readW (coeffAddr (F s₀) (8 * i + k)) 32 = BitVec.ofNat 32 ((fp s₀)[8 * i + k]!).val := by
  have fF := hp.fitF
  have c := coeff_contains (F s₀) (i := 8 * i + k) (by rw [n_eq]; omega)
  refine ⟨addr_coeff fF (by omega) (by omega), ?_, ?_⟩
  · rw [hrd, hwr, hp.rd, hp.wr]; exact inRegions_of (by simp) c
  · show coeffAt s.mem (F s₀) (8 * i + k) = _
    rw [frame_coeff hf (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
      (by rw [n_eq]; omega)]
    exact ofNat_val_eq (polyAt_val hp.red (by rw [n_eq]; omega)).symm

omit hf in
/-- Byte `S i + k` of the output: its address, and that it can be read and written. -/
theorem byte_at {S i k : Nat} (hk : S * i + k < len s₀) :
    State.addr (po s₀ + BitVec.ofNat 32 (S * i) + BitVec.ofNat 32 k) = O s₀ + BitVec.ofNat 64 (S * i + k) ∧
    InRegions s.wr (O s₀ + BitVec.ofNat 64 (S * i + k)) 1 ∧
    InRegions (s.rd ++ s.wr) (O s₀ + BitVec.ofNat 64 (S * i + k)) 1 ∧
    (outR s₀).Contains (O s₀ + BitVec.ofNat 64 (S * i + k)) 1 := by
  have fO := hp.fitO
  have c : (outR s₀).Contains (O s₀ + BitVec.ofNat 64 (S * i + k)) 1 := contains_off (by omega) (by omega)
  exact ⟨addr_byte fO rfl hk, by rw [hwr, hp.wr]; exact inRegions_of (by simp) c,
    by rw [hrd, hwr, hp.rd, hp.wr]; exact inRegions_of (by simp) c, c⟩

end

/-- Writing byte `p` of the number `X` of the group, which agrees with `A`
on the bytes before `p`. -/
theorem gb_write {s₀ : State} {i A X q p : Nat} {m : Mem} (hq : q ≤ p + 1) (hq' : p ≤ q) (hlen : dd s₀ * i + p < len s₀)
    (hL : len s₀ < 2 ^ 64) (hagree : ∀ b < p, A / 2 ^ (8 * b) % 256 = X / 2 ^ (8 * b) % 256)
    (h : GB s₀ i A q m) :
    GB s₀ i X (p + 1) (m.writeW (O s₀ + BitVec.ofNat 64 (dd s₀ * i + p)) (BitVec.ofNat 8 (X / 2 ^ (8 * p)))) := by
  intro b hb
  rw [byte_writeW8 _ _ (by omega) (by omega), h b hb]
  rcases (by omega : b < dd s₀ * i ∨ (dd s₀ * i ≤ b ∧ b < dd s₀ * i + p) ∨ b = dd s₀ * i + p ∨
    dd s₀ * i + p < b) with h' | h' | rfl | h'
  · resolve_ifs
  · resolve_ifs
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, hagree _ (by omega)]
  · resolve_ifs
    rw [Nat.add_sub_cancel_left]
  · resolve_ifs

/-! ## A field -/

/-- The fields of a group of 8: field `k` starts at bit `d k = 8 j + t`, and
spans `n` bytes, the last of them the last the fields up to `k` reach. -/
theorem fields_ok : ∀ d ∈ [5, 11], ∀ k < 8,
    d * k = 8 * (fieldAt d k).1 + (fieldAt d k).2.1 ∧ (fieldAt d k).2.1 < 8 ∧ 1 ≤ (fieldAt d k).2.2 ∧
      (fieldAt d k).2.2 ≤ 3 ∧ (fieldAt d k).1 + (fieldAt d k).2.2 ≤ d ∧
      (d * (k + 1) + 7) / 8 = (fieldAt d k).1 + (fieldAt d k).2.2 ∧
      (d * k + 7) / 8 = (fieldAt d k).1 + (if (fieldAt d k).2.1 = 0 then 0 else 1) := by
  decide

theorem enc_width : ∀ d ∈ [5, 11], encodable (BitVec.ofNat 32 d) = true := by decide

/-- The compression of coefficient `8 i + k`, as a word. -/
theorem coeff_ok {s₀ : State} (hp : Pre s₀) {i k A p : Nat} (hi : i < 32) (hk : k < 8) {s : State}
    (h : Mid s₀ i A p s) :
    WP isa (.block (ceCoeff (dd s₀) k)) s fun s' => Keeps s s' ∧ s'.mem = s.mem ∧
      s'.gpr .r1 = BitVec.ofNat 32 (cc s₀ (8 * i + k)) := by
  obtain ⟨ea, ia, va⟩ := coeff_at hp h.rd h.wr h.frame (i := i) (k := k) (by omega)
  rcases mem_widths hp.d with e | e
  · rw [e]
    refine WP.mono (coeff5_ok (by omega) h.r0 (by rw [ea]; exact ia)) fun s' ⟨k', m', r1⟩ => ⟨k', m', ?_⟩
    rw [r1, ea, va, c5_eq, cc, e]
  · rw [e]
    refine WP.mono (coeff11_ok (by omega) h.r0 (by rw [ea]; exact ia)) fun s' ⟨k', m', r1⟩ => ⟨k', m', ?_⟩
    rw [r1, ea, va, c11_eq, cc, e]

/-- The shift of `r1` after `m` of the next bytes of a field starting at
bit `t` of its first byte. -/
def rsh (t m : Nat) : Nat := if m = 0 then 0 else 8 * m - t

theorem c_toNat {c : Nat} (hc : c < 2 ^ 11) (k : Nat) : (BitVec.ofNat 32 (c / 2 ^ k)).toNat = c / 2 ^ k := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))

/-- Field `k` of group `i`. -/
theorem field_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) {k : Nat} (hk : k < 8) {s : State}
    (h : Mid s₀ i (acc s₀ i k) ((dd s₀ * k + 7) / 8) s) :
    WP isa (.block (ceField (dd s₀) k)) s
      (Mid s₀ i (acc s₀ i (k + 1)) ((dd s₀ * (k + 1) + 7) / 8)) := by
  have hd := mem_widths hp.d
  have hdl : dd s₀ ∈ [5, 11] := by rcases hd with h | h <;> rw [h] <;> decide
  obtain ⟨f0, f1, f2, f3, f4, f5, f6⟩ := fields_ok (dd s₀) hdl k hk
  have hl : len s₀ = 32 * dd s₀ := hp.len
  have hL : len s₀ < 2 ^ 64 := by rw [hl]; rcases hd with h | h <;> rw [h] <;> decide
  have hgi : dd s₀ * i + dd s₀ ≤ len s₀ := by
    rw [hl, Nat.mul_comm 32, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have hc : cc s₀ (8 * i + k) < 2 ^ 11 :=
    Nat.lt_of_lt_of_le (compress_lt _ _) (Nat.pow_le_pow_right (by decide) (by rcases hd with h | h <;> omega))
  have hA := acc_lt s₀ i k
  unfold ceField
  generalize hj : (fieldAt (dd s₀) k).1 = j at f0 f4 f5 f6
  generalize ht : (fieldAt (dd s₀) k).2.1 = t at f0 f1 f6
  generalize hn : (fieldAt (dd s₀) k).2.2 = n at f2 f3 f4 f5
  rw [f5, WP.block_append_iff, WP.block_append_iff]
  rw [f0] at hA
  -- The number of the fields up to `k`.
  have eX : acc s₀ i (k + 1) = acc s₀ i k + cc s₀ (8 * i + k) * 2 ^ (8 * j + t) := by rw [acc, f0]
  refine WP.mono (coeff_ok hp hi hk h) fun s₁ ⟨k₁, m₁, v₁⟩ => ?_
  have h₁ : Mid s₀ i (acc s₀ i k) ((dd s₀ * k + 7) / 8) s₁ := h.keeps k₁ (m₁ ▸ h.frame) (m₁ ▸ h.bytes)
  obtain ⟨eb, ob, ib, cb⟩ := byte_at hp h₁.rd h₁.wr (S := dd s₀) (i := i) (k := j) (by omega)
  -- The first byte.
  have hH : WP isa (.block (ceHead j t)) s₁ fun s₂ => Keeps s₁ s₂ ∧
      Mid s₀ i (acc s₀ i (k + 1)) (j + 1) s₂ ∧ s₂.gpr .r1 = BitVec.ofNat 32 (cc s₀ (8 * i + k)) := by
    by_cases ht0 : t = 0
    · subst ht0
      simp only [↓reduceIte, Nat.add_zero] at f6
      refine WP.mono (head0_ok (by omega) h₁.r2 (by rw [eb]; exact ob)) fun s₂ ⟨k₂, r1, m₂⟩ =>
        ⟨k₂, h₁.keeps k₂ ?_ ?_, r1.trans v₁⟩
      · rw [m₂, eb]; exact h₁.frame.writeW (List.mem_singleton_self _) _ cb
      · rw [m₂, eb, v₁]
        have ev : (BitVec.ofNat 32 (cc s₀ (8 * i + k))).setWidth 8 =
            BitVec.ofNat 8 (acc s₀ i (k + 1) / 2 ^ (8 * j)) := by
          rw [eX, add_div, Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt (by exact hA), Nat.zero_add, setWidth8,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [ev]
        refine gb_write (A := acc s₀ i k) (by omega) (by omega) (by omega) hL (fun b hb => ?_) (f6 ▸ h₁.bytes)
        rw [eX, add_bytes_lo hb]
    · simp only [ht0, ↓reduceIte] at f6
      have hr := h₁.bytes (dd s₀ * i + j) (by omega)
      rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left] at hr
      refine WP.mono (headT_ok (by omega) (by omega) h₁.r2 (by rw [eb]; exact ib) (by rw [eb]; exact ob))
        fun s₂ ⟨k₂, r1, m₂⟩ => ⟨k₂, h₁.keeps k₂ ?_ ?_, r1.trans v₁⟩
      · rw [m₂, eb]; exact h₁.frame.writeW (List.mem_singleton_self _) _ cb
      · rw [m₂, eb, v₁, hr]
        have hA' : acc s₀ i k / 2 ^ (8 * j) < 2 ^ t := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm]; exact hA
        have ht8 : 2 ^ t < 256 := Nat.pow_lt_pow_right (by decide) (by omega : t < 8)
        have ev : addB (BitVec.ofNat 8 (acc s₀ i k / 2 ^ (8 * j))) (BitVec.ofNat 32 (cc s₀ (8 * i + k)) <<< t) =
            BitVec.ofNat 8 (acc s₀ i (k + 1) / 2 ^ (8 * j)) := by
          refine byte_eq ?_
          rw [addB_toNat, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
            Nat.mod_eq_of_lt (a := cc s₀ (8 * i + k)) (by omega), eX, add_byte_j,
            Nat.mod_eq_of_lt (a := acc s₀ i k / 2 ^ (8 * j)) (by omega)]
          have e256 : ∀ a : Nat, a % 2 ^ 32 % 256 = a % 256 := fun a => by
            rw [Nat.mod_mod_of_dvd _ (by decide)]
          rw [Nat.add_mod, e256, ← Nat.add_mod]
        rw [ev]
        refine gb_write (A := acc s₀ i k) (by omega) (by omega) (by omega) hL (fun b hb => ?_) (f6 ▸ h₁.bytes)
        rw [eX, add_bytes_lo hb]
  refine WP.mono hH fun s₂ ⟨k₂, h₂, v₂⟩ => ?_
  -- The next bytes.
  refine WP.mono (wp_range_flatMap (M := isa) (f := ceNext j t) (N := n - 1)
    (fun m s' => Keeps s₂ s' ∧ Mid s₀ i (acc s₀ i (k + 1)) (j + 1 + m) s' ∧
      s'.gpr .r1 = BitVec.ofNat 32 (cc s₀ (8 * i + k) / 2 ^ rsh t m))
    (fun m s' hm ⟨k', h', v'⟩ => ?_) (n - 1) (Nat.le_refl _) s₂ ⟨Keeps.refl _, by rw [Nat.add_zero]; exact h₂, by
        rw [v₂]; simp only [rsh, ↓reduceIte, Nat.pow_zero, Nat.div_one]⟩) fun s' ⟨_, h', _⟩ => ?_
  · obtain ⟨eb', ob', -, cb'⟩ := byte_at hp h'.rd h'.wr (S := dd s₀) (i := i) (k := j + 1 + m) (by omega)
    have hsh : 1 ≤ (if m = 0 then 8 - t else 8) ∧ (if m = 0 then 8 - t else 8) ≤ 31 := by
      split <;> omega
    have eS : BitVec.ofNat 32 (cc s₀ (8 * i + k) / 2 ^ rsh t m) >>> (if m = 0 then 8 - t else 8) =
        BitVec.ofNat 32 (cc s₀ (8 * i + k) / 2 ^ rsh t (m + 1)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, c_toNat hc, c_toNat hc, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
        ← Nat.pow_add]
      refine congrArg (fun e => cc s₀ (8 * i + k) / 2 ^ e) ?_
      unfold rsh; split <;> simp <;> omega
    have ev : BitVec.ofNat 8 (cc s₀ (8 * i + k) / 2 ^ rsh t (m + 1)) =
        BitVec.ofNat 8 (acc s₀ i (k + 1) / 2 ^ (8 * (j + 1 + m))) := by
      rw [eX, show j + 1 + m = j + (m + 1) by omega, add_bytes_hi hA f1 (by omega), rsh,
        ite_eq_right (by omega)]
    refine WP.mono (next_ok (by omega) hsh h'.r2 (by rw [eb']; exact ob')) fun s₃ ⟨k₃, r1, m₃⟩ =>
      ⟨k'.trans k₃, h'.keeps k₃ ?_ ?_, ?_⟩
    · rw [m₃, eb']; exact h'.frame.writeW (List.mem_singleton_self _) _ cb'
    · rw [m₃, eb', v', eS, setWidth8, c_toNat hc, ev]
      exact gb_write (p := j + 1 + m) (by omega) (by omega) (by omega) hL (fun _ _ => rfl) h'.bytes
    · rw [r1, v', eS]
  · rw [show j + 1 + (n - 1) = j + n by omega] at h'; exact h'

/-! ## A group -/

/-- After the 8 fields, the bytes of the group are those of
`ByteEncode_d(Compress_d(f))`. -/
theorem acc_group {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) {b : Nat} (hb : b < dd s₀) :
    BitVec.ofNat 8 (acc s₀ i 8 / 2 ^ (8 * b)) = (CE s₀)[dd s₀ * i + b]! := by
  rcases mem_widths hp.d with e | e
  · have eN : acc s₀ i 8 = compress 5 (fp s₀)[8 * i]! + 32 * compress 5 (fp s₀)[8 * i + 1]! +
        1024 * compress 5 (fp s₀)[8 * i + 2]! + 32768 * compress 5 (fp s₀)[8 * i + 3]! +
        1048576 * compress 5 (fp s₀)[8 * i + 4]! + 33554432 * compress 5 (fp s₀)[8 * i + 5]! +
        1073741824 * compress 5 (fp s₀)[8 * i + 6]! + 34359738368 * compress 5 (fp s₀)[8 * i + 7]! := by
      rw [acc, acc, acc, acc, acc, acc, acc, acc, acc]
      simp only [cc, e, Nat.add_zero, Nat.reduceMul, Nat.reducePow, Nat.zero_add]
      omega
    rw [eN, CE, e]
    rw [e] at hb
    rw [compressEncode5_group (fp s₀) hi hb]
  · have eN : acc s₀ i 8 = compress 11 (fp s₀)[8 * i]! + 2048 * compress 11 (fp s₀)[8 * i + 1]! +
        4194304 * compress 11 (fp s₀)[8 * i + 2]! + 8589934592 * compress 11 (fp s₀)[8 * i + 3]! +
        17592186044416 * compress 11 (fp s₀)[8 * i + 4]! +
        36028797018963968 * compress 11 (fp s₀)[8 * i + 5]! +
        73786976294838206464 * compress 11 (fp s₀)[8 * i + 6]! +
        151115727451828646838272 * compress 11 (fp s₀)[8 * i + 7]! := by
      rw [acc, acc, acc, acc, acc, acc, acc, acc, acc]
      simp only [cc, e, Nat.add_zero, Nat.reduceMul, Nat.reducePow, Nat.zero_add]
      omega
    rw [eN, CE, e]
    rw [e] at hb
    rw [compressEncode11_group (fp s₀) hi hb]

/-- The end of an iteration. -/
theorem tail_ok {s : State} {d : Nat} {x y c : BitVec 32} (hde : encodable (BitVec.ofNat 32 d) = true)
    (h0 : s.gpr .r0 = x) (h2 : s.gpr .r2 = y) (h3 : s.gpr .r3 = c) :
    WP isa (.block ([.dp .add .r0 .r0 (.imm 32), .dp .add .r2 .r2 (.imm (BitVec.ofNat 32 d)),
      .subs .r3 .r3 (.imm 1)] : List Instr)) s fun s' =>
      s'.gpr .r0 = x + 32 ∧ s'.gpr .r2 = y + BitVec.ofNat 32 d ∧ s'.gpr .r3 = c - 1 ∧
      s'.z = (c - 1 == 0) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [hde, h0, h2, h3, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

theorem ceBody_eq (d : Nat) : ceBody d = (List.range 8).flatMap (ceField d) ++
    ([.dp .add .r0 .r0 (.imm 32), .dp .add .r2 .r2 (.imm (BitVec.ofNat 32 d)), .subs .r3 .r3 (.imm 1)] :
      List Instr) := rfl

/-- An iteration of the loop. -/
theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) {s : State} (h : Mid s₀ i 0 0 s) :
    WP isa (.block (ceBody (dd s₀))) s fun s' => Mid s₀ (i + 1) 0 0 s' ∧ s'.z = decide (i + 1 = 32) := by
  have hd := mem_widths hp.d
  have hdl : dd s₀ ∈ [5, 11] := by rcases hd with h | h <;> rw [h] <;> decide
  have hl : len s₀ = 32 * dd s₀ := hp.len
  have h0 : Mid s₀ i (acc s₀ i 0) ((dd s₀ * 0 + 7) / 8) s := by rw [Nat.mul_zero]; exact h
  rw [ceBody_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (f := ceField (dd s₀)) (N := 8)
    (fun k s => Mid s₀ i (acc s₀ i k) ((dd s₀ * k + 7) / 8) s)
    (fun k s hk hs => field_step hp hi hk hs) 8 (Nat.le_refl _) s h0) fun s₁ h₁ => ?_
  have e8 : (dd s₀ * 8 + 7) / 8 = dd s₀ := by omega
  rw [e8] at h₁
  refine WP.mono (tail_ok (enc_width _ hdl) h₁.r0 h₁.r2 h₁.r3) fun s' ⟨r0, r2, r3, z, m, rd, wr, sp, pres⟩ =>
    ⟨⟨?_, ?_, ?_, rd.trans h₁.rd, wr.trans h₁.wr, sp.trans h₁.sp,
      fun r hr => (pres r hr).trans (h₁.pres r hr), m ▸ h₁.frame, fun b hb => ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 32 i
  · rw [r2]; exact ptr_succ _ (dd s₀) i
  · rw [r3]; exact count_sub (k := 1) hi
  · rw [m, h₁.bytes b hb]
    rcases (by omega : b < dd s₀ * i ∨ (dd s₀ * i ≤ b ∧ b < dd s₀ * i + dd s₀) ∨ dd s₀ * i + dd s₀ ≤ b) with
      h' | h' | h'
    · have : b < dd s₀ * (i + 1) := by rw [Nat.mul_succ]; omega
      resolve_ifs
    · have : b < dd s₀ * (i + 1) := by rw [Nat.mul_succ]; omega
      resolve_ifs
      rw [acc_group hp hi (b := b - dd s₀ * i) (by omega), Nat.add_sub_cancel' h'.1]
    · have : ¬ b < dd s₀ * (i + 1) := by rw [Nat.mul_succ]; omega
      resolve_ifs
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-! ## The whole function -/

theorem loop_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g0 : s₁.gpr .r0 = s₀.gpr .r0)
    (g2 : s₁.gpr .r2 = s₀.gpr .r2) (g3 : s₁.gpr .r3 = BitVec.ofNat 32 (1 * 32))
    (gp : ∀ r ∈ preserved, s₁.gpr r = s₀.gpr r) (m : s₁.mem = s₀.mem) (rd : s₁.rd = s₀.rd)
    (wr : s₁.wr = s₀.wr) (sp : s₁.sp = s₀.sp) :
    WP isa (.loop (.block (ceBody (dd s₀))) .ne) s₁ fun s =>
      (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ bytesAt s.mem (O s₀) (len s₀) = CE s₀ := by
  have hlen : (CE s₀).length = len s₀ := by rw [compressEncode_length, hp.len]
  refine wp_loop_ne (fun i s => Mid s₀ i 0 0 s) (N := 32) (by decide) (fun i hi s h => step hp hi h)
    (fun s h => ⟨h.pres, h.sp, bytesAt_eq! hlen fun b hb => by
      rw [h.bytes b hb, ite_eq_left (by rw [hp.len, Nat.mul_comm] at hb; exact hb)]⟩) ?_
  refine ⟨by rw [g0]; simp, by rw [g2]; simp, by rw [g3], rd, wr, sp, gp, by rw [m]; exact Frame.refl _ _,
    fun b _ => ?_⟩
  rw [m, Nat.mul_zero, ite_eq_right (Nat.not_lt_zero _), ite_eq_right (by omega)]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compressEncode1024 s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      bytesAt s.mem (O s₀) (len s₀) = CE s₀ := by
  have hd := mem_widths hp.d
  unfold compressEncode1024
  refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
  refine WP.ite (decide (dd s₀ = 5)) (by
    show some (s₀.gpr .r1 - BitVec.ofNat 32 5 == 0) = _
    rw [cmp_z _ _ (by decide)]) (fun e => ?_) (fun e => ?_)
  · have e5 : dd s₀ = 5 := of_decide_eq_true e
    rw [← e5]
    exact loop_ok hp rfl rfl rfl (fun r hr => by
      simp only [State.setReg, subFlags]; rw [ite_eq_right (by intro e; subst e; simp [preserved] at hr)])
      rfl rfl rfl rfl
  · have e11 : dd s₀ = 11 := by have := of_decide_eq_false e; omega
    rw [← e11]
    exact loop_ok hp rfl rfl rfl (fun r hr => by
      simp only [State.setReg, subFlags]; rw [ite_eq_right (by intro e; subst e; simp [preserved] at hr)])
      rfl rfl rfl rfl

theorem pre_of {s : State} (h : (Spec.MlKem1024.compressEncodeContract Arm.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 5 | .r2 => 0x2000 | .r3 => 160 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 160⟩]

theorem verified : Verified Arm.target compressEncode1024 (Spec.MlKem1024.compressEncodeContract Arm.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.r0, .r1, .r2, .r3] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, hpres, hsp, h⟩ := correct hp
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨-, h0, h1, h2, h3⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact Add.reduced_zero _
        | decide +kernel

end VG.Proof.MlKem1024.Arm.CompressEncode
