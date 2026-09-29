import VerifiedGarbage.Proof.Hmac.X86_64.Common
import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Common
import VerifiedGarbage.Proof.Scrypt.BlockMix
import VerifiedGarbage.Impl.Scrypt.X86_64.BlockMix
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-!
# scrypt on x86-64: common lemmas

Untrusted: everything here is checked by Lean. Bytes of memory
(`Spec.Scrypt.bytesAt`) read and written, and the 64-byte exclusive-or
(`xor64`).
-/

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for `vg_scrypt_blockmix(b = rdi, r = rsi, y = rdx, ry = rcx, scratch = r8)`:
if `ry = r > 0`, writes scryptBlockMix of the `128 r` bytes at `b` to `y`.
Its call of `vg_salsa20_8` stores a return address in the 8 bytes below the
stack pointer. -/
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
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for
`vg_scrypt_romix(b = rdi, r = rsi, v = rdx, vlen = rcx, scratch = r8, slen = r9)`:
if `r > 0`, `vlen = N r` for a power of two `N`, and `slen = r + 2`, replaces
the `128 r` bytes at `b` by their scryptROMix. Its calls of
`vg_scrypt_blockmix` (and that function's of `vg_salsa20_8`) store return
addresses in the 16 bytes below the stack pointer. The indices `j` of step 3
are public. -/
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
open VG.Proof.Sha1.X86_64.Stream (Upd wp_movm wp_store)

/-! ## Addresses -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, ofInt_natCast]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem add_ofNat (a : Addr) (o j : Nat) :
    a + BitVec.ofNat 64 o + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem toNat_add_ofNat (a : Addr) {o : Nat} (h : a.toNat + o < 2 ^ 64) :
    (a + BitVec.ofNat 64 o).toNat = a.toNat + o := by
  rw [BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt h]

/-- `[a + o, a + o + n)` lies in `[a, a + len)`. -/
theorem contains_off {a : Addr} {len o n : Nat} (h : o + n ≤ len) (ho : o < 2 ^ 64) :
    (⟨a, len⟩ : Region).Contains (a + BitVec.ofNat 64 o) n := by
  simp only [Region.Contains]
  rw [show a + BitVec.ofNat 64 o - a = BitVec.ofNat 64 o by bv_omega, toNat_ofNat_lt ho]; omega

/-- `[a + o, a + o + n)` is a sub-region of `[a, a + len)`. -/
theorem sub_off {a : Addr} {len o n : Nat} (h : o + n ≤ len) (ho : o < 2 ^ 64) :
    Region.Sub ⟨a + BitVec.ofNat 64 o, n⟩ ⟨a, len⟩ := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have : (x - a).toNat ≤ (x - (a + BitVec.ofNat 64 o)).toNat + o := by
    rw [show x - a = (x - (a + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o by bv_omega,
      BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

/-- Two parts `[a + o₁, a + o₁ + n₁)` and `[a + o₂, a + o₂ + n₂)` of one
region that do not overlap. -/
theorem disj_off (a : Addr) {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁)
    (h₁ : o₁ < 2 ^ 64) (h₂ : o₂ < 2 ^ 64) (h₁' : o₁ + n₁ ≤ 2 ^ 64) (h₂' : o₂ + n₂ ≤ 2 ^ 64) :
    Region.Disjoint ⟨a + BitVec.ofNat 64 o₁, n₁⟩ ⟨a + BitVec.ofNat 64 o₂, n₂⟩ := by
  intro x hx hy
  simp only [Region.Contains] at hx hy
  have t₁ : (BitVec.ofNat 64 o₁).toNat = o₁ := toNat_ofNat_lt h₁
  have t₂ : (BitVec.ofNat 64 o₂).toNat = o₂ := toNat_ofNat_lt h₂
  bv_omega

theorem InRegions.of_mem {rs : List Region} {R : Region} (hR : R ∈ rs) {a : Addr} {n : Nat}
    (h : R.Contains a n) : InRegions rs a n := ⟨R, hR, h⟩

theorem InRegions.right {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem InRegions.left {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions rd a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_left _ hr, hc⟩

/-! ## Bytes -/

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b :=
  Proof.Hmac.X86_64.bytesAt_add m p a b

theorem bytesAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = m' (p + BitVec.ofNat 64 i)) :
    bytesAt m p n = bytesAt m' p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem frame_bytesAt {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (hl : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs :=
  Proof.Hmac.X86_64.bytesAt_writeBytes_self m q xs hl

theorem bytesAt_writeBytes_sep (m : Mem) {p q : Addr} {n : Nat} (xs : List Byte)
    (h : Region.Disjoint ⟨p, n⟩ ⟨q, xs.length⟩) (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m q xs) p n = bytesAt m p n :=
  Proof.Hmac.X86_64.bytesAt_writeBytes_sep m xs (fun x h₁ h₂ => h x h₁ h₂) hn

/-- The `64 n` bytes at `p` as `n` blocks of 64. -/
theorem bytesAt_blocks (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (64 * n) = (List.range n).flatMap fun i => bytesAt m (p + BitVec.ofNat 64 (64 * i)) 64 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, bytesAt_add, ih, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

/-- Block `i` of the bytes at `p`. -/
theorem blk_bytesAt (m : Mem) (p : Addr) {n i : Nat} (h : 64 * i + 64 ≤ n) :
    blk (bytesAt m p n) i = bytesAt m (p + BitVec.ofNat 64 (64 * i)) 64 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 64 * i + 64 + k := ⟨n - (64 * i + 64), by omega⟩
  rw [blk, bytesAt_add, bytesAt_add, List.append_assoc, List.drop_left' (bytesAt_length _ _ _),
    List.take_left' (bytesAt_length _ _ _)]

theorem xorBytes_length (a b : List Byte) (h : a.length = b.length) : (xorBytes a b).length = a.length := by
  simp [xorBytes, h]

/-! ## The 64-byte exclusive-or -/

theorem writeW_xor (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 64 ^^^ m'.readW b 64) =
      writeBytes m d (xorBytes (bytesAt m' a 8) (bytesAt m' b 8)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (64 : Nat) / 8 = 8 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    Proof.Sha256.Stream.write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Proof.Hmac.X86_64.extractLsb'_read _ _ h₁,
    Proof.Hmac.X86_64.extractLsb'_read _ _ h₁]

theorem wp_xorm {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem m) :: is)) s Q := by
  refine Proof.Sha1.X86_64.Stream.WP.cons
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
