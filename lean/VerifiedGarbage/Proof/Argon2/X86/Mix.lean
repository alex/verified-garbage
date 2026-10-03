import VerifiedGarbage.Proof.Blake2.X86.CompressB.G
import VerifiedGarbage.Proof.Argon2.Spec
import VerifiedGarbage.Impl.Argon2.X86.Compress

/-!
# Argon2 on x86 (32-bit): the steps of GB

Each step of GB (`VG.Impl.Argon2.X86.gb`) reads its operands from `scratch`
(at `esi`) and writes its result back. `addMul_ok`, `xorRot32_ok`, `xorRot_ok`
and `xorRot63_ok` give the memory each leaves, for any offsets, with the
64-bit operations on register pairs of `Proof/Sha512/X86/Rounds.lean` and
the rotations of `Proof/Blake2/X86/CompressB/G.lean`.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86
open VG.Impl.Argon2.X86 (addMul xor64m xorLd xorRot32 xorRot xorRot63)
open VG.Impl.Sha512.X86 (ld st add64 add64m)
open VG.Proof.Sha512.X86 (Only Pair Acc rd64 write64 wp_ld wp_st wp_add64 wp_add64m wp_xorS
  wp_movS mem_rd readSrc_mem lo_rd64 hi_rd64)
open VG.Proof.Sha512.Word64 (lo hi lo_xor hi_xor lo_toNat hi_toNat)
open VG.Proof.Sha256.X86.Stream (Upd Mupd)
open VG.Proof.Blake2.X86.CompressB (wp_rot wp_rot')

/-! ## States -/

/-- The registers GB writes. -/
def temps : List Reg := [.eax, .ecx, .edx]

/-- `s'` is `s` but for the registers GB writes, the flags and memory. -/
structure Keep (s s' : State) : Prop where
  gpr : ∀ r, r ∉ temps → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keep.trans {s s₁ s₂ : State} (k₁ : Keep s s₁) (k₂ : Keep s₁ s₂) : Keep s s₂ :=
  ⟨fun r hr => by rw [k₂.gpr r hr, k₁.gpr r hr], k₂.rd.trans k₁.rd, k₂.wr.trans k₁.wr⟩

theorem Keep.of_only {s s' : State} {ds : List Reg} (o : Only ds s s') (h : ∀ r ∈ ds, r ∈ temps) :
    Keep s s' :=
  ⟨fun r hr => o.gpr r fun hd => hr (h r hd), o.rd, o.wr⟩

theorem Keep.of_wrote {s s₁ s₂ : State} {ds : List Reg} {m : Mem} (o : Only ds s s₁)
    (u : Mupd s₁ s₂ m) (h : ∀ r ∈ ds, r ∈ temps) : Keep s s₂ :=
  ⟨fun r hr => by rw [u.gpr]; exact o.gpr r fun hd => hr (h r hd), u.rd.trans o.rd,
    u.wr.trans o.wr⟩

theorem Keep.esi {s s' : State} (k : Keep s s') : s'.gpr .esi = s.gpr .esi := k.gpr _ (by decide)

/-! ## `mul` -/

theorem lo_ofNat (p : Nat) : lo (BitVec.ofNat 64 p) = BitVec.ofNat 32 p := by
  apply BitVec.eq_of_toNat_eq
  rw [lo_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]

theorem hi_ofNat {p : Nat} (h : p < 2 ^ 64) : hi (BitVec.ofNat 64 p) = BitVec.ofNat 32 (p / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [hi_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega)]

theorem mul_lt (a b : BitVec 32) : a.toNat * b.toNat < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le a.isLt (Nat.le_of_lt b.isLt) (by decide))
    (by decide)

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- `mul edx`: `edx:eax := eax · edx`. -/
theorem wp_mulEdx
    (k : ∀ s', Only [.eax, .edx] s s' →
      Pair s' .eax .edx (BitVec.ofNat 64 ((s.gpr .eax).toNat * (s.gpr .edx).toNat)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.mul .edx :: rest)) s Q := by
  refine VG.Proof.Sha256.X86.Stream.WP.cons (s' := execMul .edx s) rfl (k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ⟨?_, ?_⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [execMul, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]
  · simp only [execMul, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, reduceCtorEq, ite_false, ite_true,
      lo_ofNat]
  · simp only [execMul, RegUpd.gpr_setReg, ite_true, hi_ofNat (mul_lt _ _)]

end

/-! ## `addMul` -/

theorem and_low (x : BitVec 64) : x &&& 0xffffffff = BitVec.ofNat 64 (lo x).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, lo_toNat,
    show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

theorem addMul_eq (a b : BitVec 64) :
    BitVec.ofNat 64 ((lo a).toNat * (lo b).toNat) + BitVec.ofNat 64 ((lo a).toNat * (lo b).toNat) +
      b + a = Spec.Argon2.addMul a b := by
  have hp : BitVec.ofNat 64 ((lo a).toNat * (lo b).toNat) = (a &&& 0xffffffff) * (b &&& 0xffffffff) := by
    rw [and_low, and_low, BitVec.ofNat_mul]
  rw [hp, Spec.Argon2.addMul, BitVec.mul_assoc]
  generalize (a &&& 0xffffffff) * (b &&& 0xffffffff) = x
  have two : (2 : BitVec 64) * x = x + x := by bv_omega
  rw [two]
  ac_rfl

section
variable {B : BitVec 32} {N : Nat}

theorem addMul_ok {a b : Nat} (ha : a + 8 ≤ N) (hb : b + 8 ≤ N) {s : State}
    (h0 : s.gpr .esi = B) (hA : Acc s.wr B N) :
    WP isa (.block (addMul a b)) s fun t => Keep s t ∧
      t.mem = write64 s.mem B a (Spec.Argon2.addMul (rd64 s.mem B a) (rd64 s.mem B b)) := by
  rw [← List.append_nil (addMul a b)]
  unfold addMul
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_mem h0 (mem_rd (hA b (by omega)))) fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .esi = B := by rw [u₁.other _ (by decide), h0]
  refine wp_movS (readSrc_mem b₁ (by rw [u₁.rd, u₁.wr]; exact mem_rd (hA a (by omega))))
    fun s₂ u₂ => ?_
  refine wp_mulEdx fun s₃ o₃ p₃ => ?_
  have O₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans o₃
  have b₃ : s₃.gpr .esi = B := by rw [O₃.gpr _ (by decide), h0]
  refine wp_add64 (by decide) (by decide) p₃ p₃ fun s₄ o₄ p₄ => ?_
  have O₄ := O₃.trans o₄
  have b₄ : s₄.gpr .esi = B := by rw [O₄.gpr _ (by decide), h0]
  refine wp_add64m (by decide) (by decide) b₄ (O₄.wr ▸ hA) hb p₄ fun s₅ o₅ p₅ => ?_
  have O₅ := O₄.trans o₅
  have b₅ : s₅.gpr .esi = B := by rw [O₅.gpr _ (by decide), h0]
  refine wp_add64m (by decide) (by decide) b₅ (O₅.wr ▸ hA) ha p₅ fun s₆ o₆ p₆ => ?_
  have O₆ := O₅.trans o₆
  have b₆ : s₆.gpr .esi = B := by rw [O₆.gpr _ (by decide), h0]
  refine wp_st b₆ (O₆.wr ▸ hA) ha p₆ fun s₇ u₇ => WP.block_nil
    ⟨Keep.of_wrote O₆ u₇ (by decide), ?_⟩
  have ea : s₂.gpr .eax = lo (rd64 s.mem B a) := by rw [u₂.gpr, u₁.mem, lo_rd64]
  have ed : s₂.gpr .edx = lo (rd64 s.mem B b) := by rw [u₂.other _ (by decide), u₁.gpr, lo_rd64]
  have e₄ : s₄.mem = s.mem := O₄.mem
  have e₅ : s₅.mem = s.mem := O₅.mem
  rw [u₇.mem, O₆.mem]
  simp only [e₄, e₅]
  rw [← addMul_eq, ← ea, ← ed]
/-! ## The rotations -/

theorem xorLd_ok {d a : Nat} (hd : d + 8 ≤ N) (ha : a + 8 ≤ N) {rest : List Instr} {s : State}
    {Q : State → Prop} (h0 : s.gpr .esi = B) (hA : Acc s.wr B N)
    (k : ∀ s', Only [.eax, .edx] s s' → Pair s' .eax .edx (rd64 s.mem B d ^^^ rd64 s.mem B a) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (xorLd d a ++ rest)) s Q := by
  unfold xorLd
  simp only [List.append_assoc]
  refine wp_ld (by decide) (by decide) h0 hA hd fun s₁ o₁ p₁ => ?_
  have b₁ : s₁.gpr .esi = B := by rw [o₁.gpr _ (by decide), h0]
  simp only [xor64m, VG.Impl.Sha512.X86.sc, List.cons_append, List.nil_append]
  refine wp_xorS (readSrc_mem b₁ (by rw [o₁.rd, o₁.wr]; exact mem_rd (hA a (by omega))))
    fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .esi = B := by rw [u₂.other _ (by decide), b₁]
  have r₂ : InRegions (s₂.rd ++ s₂.wr) (addr B (a + 4)) 4 := by
    rw [u₂.rd, u₂.wr, o₁.rd, o₁.wr]; exact mem_rd (hA (a + 4) (by omega))
  refine wp_xorS (readSrc_mem b₂ r₂) fun s₃ u₃ =>
    k s₃ ((o₁.trans (Only.of_upd u₂)).trans (Only.of_upd u₃) |>.mono (by decide)) ⟨?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr, p₁.1, o₁.mem]; simp only [lo_xor, lo_rd64]
  · rw [u₃.gpr, u₂.other _ (by decide), p₁.2, u₂.mem, o₁.mem]; simp only [hi_xor, hi_rd64]

theorem xorRot32_ok {d a : Nat} (hd : d + 8 ≤ N) (ha : a + 8 ≤ N) {s : State}
    (h0 : s.gpr .esi = B) (hA : Acc s.wr B N) :
    WP isa (.block (xorRot32 d a)) s fun t => Keep s t ∧
      t.mem = write64 s.mem B d ((rd64 s.mem B d ^^^ rd64 s.mem B a).rotateRight 32) := by
  rw [← List.append_nil (xorRot32 d a)]
  unfold xorRot32
  simp only [List.append_assoc]
  refine xorLd_ok hd ha h0 hA fun s₁ o₁ p₁ => ?_
  refine wp_st (by rw [o₁.gpr _ (by decide), h0]) (o₁.wr ▸ hA) hd p₁.swap fun s₂ u₂ =>
    WP.block_nil ⟨Keep.of_wrote o₁ u₂ (by decide), by rw [u₂.mem, o₁.mem]⟩

theorem xorRot_ok {d a n : Nat} (hn : 0 < n) (hn' : n < 32) (hd : d + 8 ≤ N) (ha : a + 8 ≤ N)
    {s : State} (h0 : s.gpr .esi = B) (hA : Acc s.wr B N) :
    WP isa (.block (xorRot d a n)) s fun t => Keep s t ∧
      t.mem = write64 s.mem B d ((rd64 s.mem B d ^^^ rd64 s.mem B a).rotateRight n) := by
  rw [← List.append_nil (xorRot d a n)]
  unfold xorRot
  simp only [List.append_assoc]
  refine xorLd_ok hd ha h0 hA fun s₁ o₁ p₁ => ?_
  refine wp_rot hn hn' (by decide) (by decide) (by decide) p₁ fun s₂ o₂ p₂ => ?_
  have O := o₁.trans o₂
  refine wp_st (by rw [O.gpr _ (by decide), h0]) (O.wr ▸ hA) hd p₂ fun s₃ u₃ =>
    WP.block_nil ⟨Keep.of_wrote O u₃ (by decide), by rw [u₃.mem, O.mem]⟩

theorem xorRot63_ok {d a : Nat} (hd : d + 8 ≤ N) (ha : a + 8 ≤ N) {s : State}
    (h0 : s.gpr .esi = B) (hA : Acc s.wr B N) :
    WP isa (.block (xorRot63 d a)) s fun t => Keep s t ∧
      t.mem = write64 s.mem B d ((rd64 s.mem B d ^^^ rd64 s.mem B a).rotateRight 63) := by
  rw [← List.append_nil (xorRot63 d a)]
  unfold xorRot63
  simp only [List.append_assoc]
  refine xorLd_ok hd ha h0 hA fun s₁ o₁ p₁ => ?_
  refine wp_rot' (by decide) (by decide) (by decide) (by decide) (by decide) p₁ fun s₂ o₂ p₂ => ?_
  have O := o₁.trans o₂
  refine wp_st (by rw [O.gpr _ (by decide), h0]) (O.wr ▸ hA) hd p₂ fun s₃ u₃ =>
    WP.block_nil ⟨Keep.of_wrote O u₃ (by decide), by rw [u₃.mem, O.mem]⟩

end

end VG.Proof.Argon2.X86
