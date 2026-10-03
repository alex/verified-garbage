import VerifiedGarbage.Proof.Scrypt.X86.Salsa
import VerifiedGarbage.Proof.Scrypt.BlockMix
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Impl.Scrypt.X86.BlockMix

/-!
# scrypt on x86 (32-bit): common lemmas

The target-independent lemmas about addresses and bytes are in
`Proof/Scrypt/Memory.lean`; here are 32-bit pointers as addresses, `mul`, the
64-byte exclusive-or, and saving and restoring registers.
-/

namespace VG.Proof.Scrypt.X86

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movi wp_movm wp_store)
open VG.Proof.Scrypt.Memory (sub_off xorBytes_length bytesAt_length bytesAt_add
  bytesAt_writeBytes_sep)

/-! ## 32-bit pointers -/

theorem toNat_add32 {p : BitVec 32} {o : Nat} (h : p.toNat + o < 2 ^ 32) :
    (p + BitVec.ofNat 32 o).toNat = p.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega),
    Nat.mod_eq_of_lt h]

theorem add32 (p : BitVec 32) (o j : Nat) :
    p + BitVec.ofNat 32 o + BitVec.ofNat 32 j = p + BitVec.ofNat 32 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- A register plus a small constant, as the code writes it. -/
theorem add32_lit (p : BitVec 32) (o j : Nat) :
    p + BitVec.ofNat 32 o + (OfNat.ofNat j : BitVec 32) =
      p + BitVec.ofNat 32 (o + (OfNat.ofNat j : Nat)) :=
  add32 p o j

theorem sub32 (p : BitVec 32) {o : Nat} (h : 64 ≤ o) :
    p + BitVec.ofNat 32 o - 64 = p + BitVec.ofNat 32 (o - 64) := by
  rw [show o = (o - 64) + 64 by omega, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem ofNat_toNat32 (x : BitVec 32) : x = BitVec.ofNat 32 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ofNat_pred32 {k : Nat} (h : 1 ≤ k) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, BitVec.ofNat_add, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

/-- `[p + o]`, for a pointer `p` into a region that does not wrap around. -/
theorem addr_add {p : BitVec 32} {o : Nat} (h : p.toNat + o < 2 ^ 32) :
    (p + BitVec.ofNat 32 o).setWidth 64 = p.setWidth 64 + BitVec.ofNat 64 o := by
  have := addr_eq (x := p) (k := o) h
  exact this

/-- `[(p + o) + d]`, where nothing wraps around. -/
theorem addr_off {p : BitVec 32} {o d : Nat} (h : p.toNat + o + d < 2 ^ 32) :
    addr (p + BitVec.ofNat 32 o) d = p.setWidth 64 + BitVec.ofNat 64 o + BitVec.ofNat 64 d := by
  rw [Proof.Sha256.X86.Stream.addr_add_ofNat h, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem addr_zero (p : BitVec 32) : addr p 0 = p.setWidth 64 := by
  simp [addr]

/-- `and d, r` -/
theorem wp_and {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d &&& s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-! ## `mul` -/

/-- `mul r`: `eax` is the low half of `eax * r`; `edx` and the flags change too. -/
theorem wp_mul {is : List Instr} {s : State} {Q : State → Prop} {r : Reg}
    (k : ∀ s', s'.gpr .eax = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat) →
      (∀ q, q ≠ .eax → q ≠ .edx → s'.gpr q = s.gpr q) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.mul r :: is)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons rfl (k _ (by simp [execMul, State.setReg])
    (fun q h₁ h₂ => by simp [execMul, State.setReg, State.setFlags, h₁, h₂]) rfl rfl rfl)

/-- `timesR m`: `eax = m r`, for the word `r` at `[esp + 8]`. -/
theorem timesR_ok {m : BitVec 32} {s : State} {r : BitVec 32}
    (hr : s.mem.readW (addr (s.gpr .esp) 8) 32 = r) (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .eax = BitVec.ofNat 32 (r.toNat * m.toNat) →
      (∀ q, q ≠ .eax → q ≠ .ecx → q ≠ .edx → s'.gpr q = s.gpr q) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block rest) s' Q) :
    WP isa (.block (timesR m ++ rest)) s Q := by
  refine wp_movm (a := addr (s.gpr .esp) 8) rfl hin fun s₁ u₁ => wp_movi fun s₂ u₂ => ?_
  refine wp_mul fun s₃ e₃ o₃ m₃ rd₃ wr₃ => k s₃ ?_ (fun q h1 h2 h3 => ?_) (by rw [m₃, u₂.mem, u₁.mem])
    (by rw [rd₃, u₂.rd, u₁.rd]) (by rw [wr₃, u₂.wr, u₁.wr])
  · rw [e₃, u₂.other _ (by decide), u₁.gpr, hr, u₂.gpr]
  · rw [o₃ q h1 h3, u₂.other q h2, u₁.other q h1]

/-! ## Words of bytes -/

theorem writeW_xor32 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 32 ^^^ m'.readW b 32) =
      writeBytes m d (xorBytes (bytesAt m' a 4) (bytesAt m' b 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    Proof.Sha256.Stream.write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁,
    Mem.extractLsb'_read _ _ h₁]

/-- One more word of `[d] ← [x] xor [y]`. -/
theorem xor_mem4 (m : Mem) {d x y : Addr} {n k : Nat} (hk : k < n) (hlt : 4 * n < 2 ^ 64)
    (hdx : Region.Disjoint ⟨d, 4 * n⟩ ⟨x, 4 * n⟩) (hdy : Region.Disjoint ⟨d, 4 * n⟩ ⟨y, 4 * n⟩) :
    (writeBytes m d (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k)))).writeW
      (d + BitVec.ofNat 64 (4 * k))
      ((writeBytes m d (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k)))).readW
          (x + BitVec.ofNat 64 (4 * k)) 32 ^^^
        (writeBytes m d (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k)))).readW
          (y + BitVec.ofNat 64 (4 * k)) 32) =
      writeBytes m d (xorBytes (bytesAt m x (4 * (k + 1))) (bytesAt m y (4 * (k + 1)))) := by
  have hl : (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k))).length = 4 * k := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (4 * k), 4⟩
      ⟨d, (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k))).length⟩ := by
    rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (4 * k), 4⟩
      ⟨d, (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k))).length⟩ := by
    rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  rw [writeW_xor32, bytesAt_writeBytes_sep _ _ sx (by omega),
    bytesAt_writeBytes_sep _ _ sy (by omega)]
  have e := writeBytes_append m d _ (xorBytes (bytesAt m (x + BitVec.ofNat 64 (4 * k)) 4)
    (bytesAt m (y + BitVec.ofNat 64 (4 * k)) 4))
    (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
  rw [hl] at e
  rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
    List.zipWith_append (by simp [bytesAt])]

/-! ## The 64-byte exclusive-or -/

/-- The first `n` words of `[dst] ← [x] xor [src]`, for 64-byte blocks at
`d`, `x`, `y`, where `d` overlaps neither of the others. The code uses
`eax`. -/
theorem xor64_ok {dR xR sR : Reg} (hd : dR ≠ .eax) (hx : xR ≠ .eax) (hs : sR ≠ .eax)
    {d x y : BitVec 32} (fd : d.toNat + 64 ≤ 2 ^ 32) (fx : x.toNat + 64 ≤ 2 ^ 32)
    (fy : y.toNat + 64 ≤ 2 ^ 32)
    (hdx : Region.Disjoint ⟨d.setWidth 64, 64⟩ ⟨x.setWidth 64, 64⟩)
    (hdy : Region.Disjoint ⟨d.setWidth 64, 64⟩ ⟨y.setWidth 64, 64⟩) :
    ∀ n ≤ 16, ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr dR = d → s.gpr xR = x → s.gpr sR = y →
    (∀ k < 16, InRegions (s.rd ++ s.wr) (x.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < 16, InRegions (s.rd ++ s.wr) (y.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < 16, InRegions s.wr (d.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (d.setWidth 64)
        (xorBytes (bytesAt s.mem (x.setWidth 64) (4 * n)) (bytesAt s.mem (y.setWidth 64) (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (xorW dR xR sR) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q gd gx gy hinx hiny hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q gd gx gy hinx hiny hout fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    refine wp_movm (a := x.setWidth 64 + BitVec.ofNat 64 (4 * n))
      (by rw [ea_at, g₁ _ hx, gx]; exact addr_eq (by omega)) (by rw [rd₁, wr₁]; exact hinx n (by omega))
      fun s₂ u₂ => ?_
    refine wp_xorm (a := y.setWidth 64 + BitVec.ofNat 64 (4 * n))
      (by rw [ea_at, u₂.other _ hs, g₁ _ hs, gy]; exact addr_eq (by omega))
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact hiny n (by omega)) fun s₃ u₃ => ?_
    refine wp_store (a := d.setWidth 64 + BitVec.ofNat 64 (4 * n))
      (by rw [ea_at, u₃.other _ hd, u₂.other _ hd, g₁ _ hd, gd]; exact addr_eq (by omega))
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      fun s₄ u₄ => k s₄ (fun r h => by rw [u₄.gpr, u₃.other r h, u₂.other r h, g₁ r h])
        (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]) ?_
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, m₁]
    exact xor_mem4 s.mem (n := 16) (by omega) (by omega) hdx hdy

/-! ## Counted loops -/

/-- A do-while loop over `ne` that runs its body `n > 0` times, with ZF set
exactly on the last iteration. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ s'.zf = some (decide (k + 1 = n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (k + 1 = n)) := by
    show s'.zf.map (!·) = _; rw [hz]; rfl
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [he]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [he]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-- The count after one more iteration of `n`. -/
theorem dec_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 32 (n - k) - 1 = BitVec.ofNat 32 (n - (k + 1)) := by
  rw [ofNat_pred32 (by omega), Nat.sub_sub]

theorem dec_z {n k : Nat} (hk : k < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - k) - 1 == 0) = decide (k + 1 = n) := by
  rw [dec_count hk, Proof.Sha256.X86.Stream.ofNat_beq_zero (by omega)]
  exact decide_eq_decide.mpr (by omega)

end VG.Proof.Scrypt.X86
