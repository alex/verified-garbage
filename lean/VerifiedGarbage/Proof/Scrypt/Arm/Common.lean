import VerifiedGarbage.Proof.Scrypt.Arm.Salsa
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Impl.Scrypt.Arm.BlockMix

/-!
# scrypt on 32-bit ARM: common lemmas

Untrusted: everything here is checked by Lean. The target-independent lemmas
about addresses and bytes are in `Proof/Scrypt/Memory.lean`; here are
32-bit pointers as addresses, and the 64-byte exclusive-or.
-/

namespace VG.Proof.Scrypt.Arm

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)
open VG.Proof.MdStream.Arm (Upd Mupd wp_ldr wp_str op2_reg saveMem)
open VG.Proof.Hmac.Arm.Init (wp_eor)
open VG.Proof.Scrypt.Memory (sub_off xorBytes_length bytesAt_length bytesAt_add
  bytesAt_writeBytes_sep)

/-! ## 32-bit pointers -/

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

theorem toNat_add32 {p : BitVec 32} {o : Nat} (h : p.toNat + o < 2 ^ 32) :
    (p + BitVec.ofNat 32 o).toNat = p.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega),
    Nat.mod_eq_of_lt h]

theorem add32 (p : BitVec 32) (o j : Nat) :
    p + BitVec.ofNat 32 o + BitVec.ofNat 32 j = p + BitVec.ofNat 32 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- A pointer plus two offsets, as an address. -/
theorem addr_add2 {p : BitVec 32} {o j : Nat} (h : p.toNat + o + j < 2 ^ 32) :
    State.addr (p + BitVec.ofNat 32 o + BitVec.ofNat 32 j) =
      State.addr p + BitVec.ofNat 64 o + BitVec.ofNat 64 j := by
  rw [add32, addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]

theorem sub32 (p : BitVec 32) {o : Nat} (h : 64 ≤ o) :
    p + BitVec.ofNat 32 o - 64 = p + BitVec.ofNat 32 (o - 64) := by
  rw [show o = (o - 64) + 64 by omega, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem shl32 {x : BitVec 32} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 32) :
    x <<< n = BitVec.ofNat 32 (x.toNat * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

/-- A register plus a small constant, as the code writes it. -/
theorem add32_lit (p : BitVec 32) (o j : Nat) :
    p + BitVec.ofNat 32 o + (OfNat.ofNat j : BitVec 32) =
      p + BitVec.ofNat 32 (o + (OfNat.ofNat j : Nat)) :=
  add32 p o j

theorem ofNat_pred32 {k : Nat} (h : 1 ≤ k) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, BitVec.ofNat_add, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem ofNat_toNat32 (x : BitVec 32) : x = BitVec.ofNat 32 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

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
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁]

/-! ## The 64-byte exclusive-or -/

/-- The first `n` words of `[dst] ← [x] xor [src]`, for 64-byte blocks at
`d`, `x`, `y`, where `d` overlaps neither of the others. The code uses `r2`
and `r3`. -/
theorem xor64_ok {dR xR sR : Reg} (hd : dR ≠ .r2 ∧ dR ≠ .r3) (hx : xR ≠ .r2 ∧ xR ≠ .r3)
    (hs : sR ≠ .r2 ∧ sR ≠ .r3) {d x y : BitVec 32} (fd : d.toNat + 64 ≤ 2 ^ 32)
    (fx : x.toNat + 64 ≤ 2 ^ 32) (fy : y.toNat + 64 ≤ 2 ^ 32)
    (hdx : Region.Disjoint ⟨State.addr d, 64⟩ ⟨State.addr x, 64⟩)
    (hdy : Region.Disjoint ⟨State.addr d, 64⟩ ⟨State.addr y, 64⟩) :
    ∀ n ≤ 16, ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr dR = d → s.gpr xR = x → s.gpr sR = y →
    (∀ k < 16, InRegions (s.rd ++ s.wr) (State.addr x + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < 16, InRegions (s.rd ++ s.wr) (State.addr y + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < 16, InRegions s.wr (State.addr d + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr d)
        (xorBytes (bytesAt s.mem (State.addr x) (4 * n)) (bytesAt s.mem (State.addr y) (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (xorW dR xR sR) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [bytesAt, xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q gd gx gy hinx hiny hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q gd gx gy hinx hiny hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    refine wp_ldr (a := State.addr x + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [g₁ _ hx.1 hx.2, gx, addr_add (by omega)]) (by rw [rd₁, wr₁]; exact hinx n (by omega))
      fun s₂ u₂ => ?_
    refine wp_ldr (a := State.addr y + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [u₂.other _ hs.1, g₁ _ hs.1 hs.2, gy, addr_add (by omega)])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact hiny n (by omega)) fun s₃ u₃ => ?_
    refine wp_eor (op2_reg _ _) fun s₄ u₄ => ?_
    refine wp_str (a := State.addr d + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [u₄.other _ hd.1, u₃.other _ hd.2, u₂.other _ hd.1, g₁ _ hd.1 hd.2, gd,
        addr_add (by omega)])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      fun s₅ u₅ => k s₅ (fun r h2 h3 => by
          rw [u₅.gpr, u₄.other r h2, u₃.other r h3, u₂.other r h2, g₁ r h2 h3])
        (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : (xorBytes (bytesAt s.mem (State.addr x) (4 * n))
        (bytesAt s.mem (State.addr y) (4 * n))).length = 4 * n := by
      rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    have sx : Region.Disjoint ⟨State.addr x + BitVec.ofNat 64 (4 * n), 4⟩
        ⟨State.addr d, (xorBytes (bytesAt s.mem (State.addr x) (4 * n))
          (bytesAt s.mem (State.addr y) (4 * n))).length⟩ := by
      rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    have sy : Region.Disjoint ⟨State.addr y + BitVec.ofNat 64 (4 * n), 4⟩
        ⟨State.addr d, (xorBytes (bytesAt s.mem (State.addr x) (4 * n))
          (bytesAt s.mem (State.addr y) (4 * n))).length⟩ := by
      rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₃.mem, u₂.mem, writeW_xor32,
      m₁, bytesAt_writeBytes_sep _ _ sx (by omega), bytesAt_writeBytes_sep _ _ sy (by omega)]
    have e := writeBytes_append s.mem (State.addr d) _
      (xorBytes (bytesAt s.mem (State.addr x + BitVec.ofNat 64 (4 * n)) 4)
        (bytesAt s.mem (State.addr y + BitVec.ofNat 64 (4 * n)) 4))
      (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
    rw [hl] at e
    rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
      List.zipWith_append (by simp [bytesAt])]

/-! ## Saving and restoring our caller's registers -/

/-- The stores of `saveMem` stay in `R`. -/
theorem saveMem_frame' {R : Region} {B : Addr} (g : Reg → BitVec 32) :
    ∀ (l : List (Reg × Nat)) (m : Mem), (∀ p ∈ l, R.Contains (B + BitVec.ofNat 64 p.2) 4) →
      Frame [R] m (saveMem m B g l) := by
  intro l
  induction l with
  | nil => intro m _; exact Frame.refl _ _
  | cons p l ih =>
    intro m hl
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hl p (by simp))).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

/-- Loading the registers `l` through the pointer in `b`, which none of them is. -/
theorem restoreList_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ b ∧ p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 b p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h2, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldr h1 (addr_add h2) h3 fun s₁ u₁ => ?_
    have eb : s₁.gpr b = s.gpr b := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr hsp => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp)
    · rw [eb, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

end VG.Proof.Scrypt.Arm
