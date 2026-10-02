import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.Scrypt.BlockMix
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Impl.Scrypt.X86_64.BlockMix
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Offset

/-!
# scrypt on x86-64: common lemmas

The contracts the proofs are written against, and the 64-byte exclusive-or
(`xor64`); the target-independent memory lemmas are in
`VG.Proof.Scrypt.Memory`.
-/

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.X86_64 in
/-- X86-64 contract for `vg_scrypt_blockmix(b = rdi, r = rsi, y = rdx, ry = rcx,
scratch = r8)`: if `ry = r > 0`, writes scryptBlockMix of the `128 r` bytes at
`b` to `y`. Its call of `vg_salsa20_8` stores a return address in the 8 bytes
below the stack pointer. -/
def blockMixX86_64 : Contract X86_64.isa where
  pre s :=
    let r := (s.gpr .rsi).toNat
    let b : Region := ⟨s.gpr .rdi, r * 128⟩
    let y : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .r8, 128⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [b] ∧ s.wr = [y, scratch] ∧
    y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧
    ret.Disjoint y ∧ ret.Disjoint scratch ∧
    stack.Disjoint b ∧ stack.Disjoint y ∧ stack.Disjoint scratch ∧
    (s.gpr .rdi).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + 128 ≤ 2 ^ 64 ∧
    s.gpr .rcx = s.gpr .rsi ∧ 0 < r
  post s s' := let r := (s.gpr .rsi).toNat
    bytesAt s'.mem (s.gpr .rdx) (128 * r) = blockMix r (bytesAt s.mem (s.gpr .rdi) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- X86-64 contract for `vg_scrypt_romix(b = rdi, r = rsi, v = rdx, vlen = rcx,
scratch = r8, slen = r9)`: if `r > 0`, `vlen = N r` for a power of two `N`, and
`slen = r + 2`, replaces the `128 r` bytes at `b` by their scryptROMix. Its
calls of `vg_scrypt_blockmix` (and that function's of `vg_salsa20_8`) store
return addresses in the 16 bytes below the stack pointer. The indices `j` of
step 3 are public. -/
def roMixX86_64 : Contract X86_64.isa where
  pre s :=
    let r := (s.gpr .rsi).toNat
    let b : Region := ⟨s.gpr .rdi, r * 128⟩
    let v : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 128⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    s.rd = [] ∧ s.wr = [b, v, scratch] ∧
    b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
    ret.Disjoint b ∧ ret.Disjoint v ∧ ret.Disjoint scratch ∧
    stack.Disjoint b ∧ stack.Disjoint v ∧ stack.Disjoint scratch ∧
    (s.gpr .rdi).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat * 128 ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .rcx).toNat % r = 0 ∧ ((s.gpr .rcx).toNat / r).isPowerOfTwo ∧
    (s.gpr .r9).toNat = r + 2
  post s s' := let r := (s.gpr .rsi).toNat
    bytesAt s'.mem (s.gpr .rdi) (128 * r) =
      roMix r ((s.gpr .rcx).toNat / r) (bytesAt s.mem (s.gpr .rdi) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧
    roMixIndices (s₁.gpr .rsi).toNat ((s₁.gpr .rcx).toNat / (s₁.gpr .rsi).toNat)
        (bytesAt s₁.mem (s₁.gpr .rdi) (128 * (s₁.gpr .rsi).toNat)) =
      roMixIndices (s₂.gpr .rsi).toNat ((s₂.gpr .rcx).toNat / (s₂.gpr .rsi).toNat)
        (bytesAt s₂.mem (s₂.gpr .rdi) (128 * (s₂.gpr .rsi).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.X86_64.BlockMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)
open VG.Proof.MdStream.X86_64 (Upd wp_movm wp_store)
open VG.Proof.Scrypt.Memory (sub_off bytesAt_add bytesAt_length bytesAt_writeBytes_sep xorBytes_length
  writeW_xor)

/-! ## Addresses -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, ofInt_natCast]

/-! ## The 64-byte exclusive-or -/

theorem wp_xorm {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem m) :: is)) s Q := by
  refine Proof.MdStream.X86_64.WP.cons
    (s' := (arithFlags s (s.gpr d ^^^ s.mem.readW a 64) false false).setReg d _) ?_
    (k _ (Upd.flags _ _ _ _ _ _))
  simp [exec, execAlu, readSrc, State.load64, ha, hin]

/-- The first `n` words of `[dst] ← [x] xor [src]`, for 64-byte blocks `d`,
`x`, `y` in memory, where `d` overlaps neither of the others. -/
theorem xor64_ok {dR xR sR : Reg} (hd : dR ≠ .rax) (hx : xR ≠ .rax) (hs : sR ≠ .rax)
    {d x y : Addr} (hdx : Region.Disjoint ⟨d, 64⟩ ⟨x, 64⟩) (hdy : Region.Disjoint ⟨d, 64⟩ ⟨y, 64⟩) :
    ∀ n ≤ 8, ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr dR = d → s.gpr xR = x → s.gpr sR = y →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < 8, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))) →
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
    refine wp_movm (a := x + BitVec.ofNat 64 (8 * n))
      (by rw [ea_at, g₁ _ hx, gx]) (by rw [rd₁, wr₁]; exact hinx n (by omega)) fun s₂ u₂ => ?_
    refine wp_xorm (a := y + BitVec.ofNat 64 (8 * n))
      (by rw [ea_at, u₂.other _ hs, g₁ _ hs, gy])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact hiny n (by omega)) fun s₃ u₃ => ?_
    refine wp_store (a := d + BitVec.ofNat 64 (8 * n))
      (by rw [ea_at, u₃.other _ hd, u₂.other _ hd, g₁ _ hd, gd])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      fun s₄ g₄ m₄ rd₄ wr₄ => k s₄ (fun r hr => by rw [g₄, u₃.other r hr, u₂.other r hr, g₁ r hr])
        (by rw [rd₄, u₃.rd, u₂.rd, rd₁]) (by rw [wr₄, u₃.wr, u₂.wr, wr₁]) ?_
    have hl : (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))).length = 8 * n := by
      rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    -- The words of `x` and `y` are not in the part of `d` written so far.
    have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (8 * n), 8⟩ ⟨d, (xorBytes (bytesAt s.mem x (8 * n))
        (bytesAt s.mem y (8 * n))).length⟩ := by
      rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (8 * n), 8⟩ ⟨d, (xorBytes (bytesAt s.mem x (8 * n))
        (bytesAt s.mem y (8 * n))).length⟩ := by
      rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    rw [m₄, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, writeW_xor, m₁, bytesAt_writeBytes_sep _ _ sx (by omega),
      bytesAt_writeBytes_sep _ _ sy (by omega)]
    have e := writeBytes_append s.mem d _ (xorBytes (bytesAt s.mem (x + BitVec.ofNat 64 (8 * n)) 8)
      (bytesAt s.mem (y + BitVec.ofNat 64 (8 * n)) 8))
      (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
    rw [hl] at e
    rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
      List.zipWith_append (by simp [bytesAt])]

end VG.Proof.Scrypt.X86_64.BlockMix
