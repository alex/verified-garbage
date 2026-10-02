import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Impl.Aes.X86_64.AesNi
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gcm.X86_64.Rev

section

/-!
# AES-NI: the instructions are FIPS 197's rounds

An SSE register holds an AES state as its 16 bytes in memory order (`st`):
byte `r + 4c` is `s[r, c]`, as FIPS 197 §3.4 lays the state out and as the
SDM's AES instructions read it. On such registers `pxor`, `aesenc` and
`aesenclast` are `AddRoundKey`, a full round and the last round of
`Spec.Aes.cipher` (`pxor_st`, `aesenc_st`, `aesenclast_st`); the S-box of the
ISA model, computed by repeated squaring, is the one of `Spec/Aes.lean`
(`sbox_eq`).
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG.X86_64
open VG.Spec.Aes (subBytes shiftRows mixColumns addRoundKey sbox roundKey cipher bytesAt)

/-! ## GF(2⁸) -/

theorem mul_eq : aesMul = Spec.Aes.mul := rfl

/-- Both square and multiply `b²`, `b⁴`, …, `b¹²⁸` in the same order: unfolded
to the same term (no evaluation left for the kernel). -/
theorem inv_eq (b : BitVec 8) : aesInv b = Spec.Aes.inv b := by
  simp (config := {decide := true}) only [aesInv, Spec.Aes.inv, Spec.Aes.pow, List.range_succ,
    List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, mul_eq,
    ite_true, ite_false]

theorem sbox_eq : aesSbox = sbox := by
  funext b
  simp only [aesSbox, sbox, inv_eq, ofBits8]

theorem mul_one' : ∀ b : BitVec 8, Spec.Aes.mul 1 b = b := by decide +kernel

/-! ## States in registers -/

/-- The AES state held by a register. -/
def st (v : BitVec 128) : Spec.Aes.State := Vector.ofFn fun i => byte v i

theorem getD_ofFn {f : Fin 16 → Byte} {i : Nat} (h : i < 16) :
    (Vector.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  simp [Vector.getD, h]

theorem getD_st (v : BitVec 128) {i : Nat} (h : i < 16) : (st v).getD i 0 = byte v i := by
  rw [st, getD_ofFn h]

theorem st_ext {s t : Spec.Aes.State} (h : ∀ i < 16, s.getD i 0 = t.getD i 0) : s = t := by
  apply Vector.ext; intro i hi
  have := h i hi
  simpa [Vector.getD, hi] using this

theorem st_inj {a b : BitVec 128} (h : st a = st b) : a = b :=
  VG.Proof.Gcm.X86_64.ext_byte fun i hi => by rw [← getD_st a hi, ← getD_st b hi, h]

theorem byte_xor (a b : BitVec 128) (i : Nat) : byte (a ^^^ b) i = byte a i ^^^ byte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hj, decide_true, Bool.true_and]

/-! ## FIPS 197's transformations, byte by byte -/

theorem getD_addRoundKey (s : Spec.Aes.State) (rk : List Byte) {i : Nat} (h : i < 16) :
    (addRoundKey s rk).getD i 0 = s.getD i 0 ^^^ rk.getD i 0 := by
  rw [addRoundKey, getD_ofFn h]

theorem getD_subBytes (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (subBytes s).getD i 0 = sbox (s.getD i 0) := by
  simp [subBytes, Vector.getD, h]

theorem getD_shiftRows (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (shiftRows s).getD i 0 = s.getD (i % 4 + 4 * ((i / 4 + i % 4) % 4)) 0 := by
  rw [shiftRows, getD_ofFn h]

theorem getD_mixColumns (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (mixColumns s).getD i 0 =
      Spec.Aes.mul 0x02 (s.getD ((i % 4 + 0) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x03 (s.getD ((i % 4 + 1) % 4 + 4 * (i / 4)) 0) ^^^
      s.getD ((i % 4 + 2) % 4 + 4 * (i / 4)) 0 ^^^ s.getD ((i % 4 + 3) % 4 + 4 * (i / 4)) 0 := by
  rw [mixColumns, getD_ofFn h]

theorem byte_mapBytes (f : BitVec 8 → BitVec 8) (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesMapBytes f x) i = f (byte x i) := by
  rw [aesMapBytes, VG.Proof.Gcm.X86_64.byte_ofBytes _ h]

theorem byte_shiftRows (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesShiftRows x) i = byte x (i % 4 + 4 * ((i / 4 + i % 4) % 4)) := by
  rw [aesShiftRows, VG.Proof.Gcm.X86_64.byte_ofBytes _ h]

theorem byte_mixColumns (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesMixColumns x) i =
      aesMul 0x02 (byte x ((i % 4 + 0) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x03 (byte x ((i % 4 + 1) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (byte x ((i % 4 + 2) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (byte x ((i % 4 + 3) % 4 + 4 * (i / 4))) := by
  rw [aesMixColumns, aesMixWith, VG.Proof.Gcm.X86_64.byte_ofBytes _ h]

/-! ## The instructions -/

/-- `pxor` with a round key is `AddRoundKey`. -/
theorem pxor_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    st (XBinOp.eval .pxor v k) = addRoundKey (st v) rk := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, getD_addRoundKey _ _ hi, getD_st _ hi, ← hk i hi]
  exact byte_xor v k i

/-- `aesenc` is a round. -/
theorem aesenc_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    st (XBinOp.eval .aesenc v k) = addRoundKey (mixColumns (shiftRows (subBytes (st v)))) rk := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, getD_addRoundKey _ _ hi, getD_mixColumns _ hi, ← hk i hi]
  simp only [XBinOp.eval, byte_xor]
  rw [byte_mixColumns _ hi]
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + j % 4) % 4) < 16 := fun j => by omega
  simp only [byte_mapBytes _ _ (hr _), getD_shiftRows _ (hr _), byte_shiftRows _ (hr _), sbox_eq,
    mul_eq, mul_one', getD_subBytes _ (hs _), getD_st _ (hs _)]

/-- `aesenclast` is the last round. -/
theorem aesenclast_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    st (XBinOp.eval .aesenclast v k) = addRoundKey (shiftRows (subBytes (st v))) rk := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, getD_addRoundKey _ _ hi, ← hk i hi]
  simp only [XBinOp.eval, byte_xor]
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + j % 4) % 4) < 16 := fun j => by omega
  simp only [byte_mapBytes _ _ hi, getD_shiftRows _ hi, byte_shiftRows _ hi, sbox_eq,
    getD_subBytes _ (hs _), getD_st _ (hs _)]

/-! ## The cipher -/

/-- The state after `AddRoundKey` and `k` full rounds. -/
def rnds (w : List Byte) (x : Spec.Aes.State) (k : Nat) : Spec.Aes.State :=
  (List.range k).foldl
    (fun s j => addRoundKey (mixColumns (shiftRows (subBytes s))) (roundKey w (j + 1)))
    (addRoundKey x (roundKey w 0))

theorem rnds_zero (w : List Byte) (x : Spec.Aes.State) :
    rnds w x 0 = addRoundKey x (roundKey w 0) := rfl

theorem rnds_succ (w : List Byte) (x : Spec.Aes.State) (k : Nat) :
    rnds w x (k + 1) =
      addRoundKey (mixColumns (shiftRows (subBytes (rnds w x k)))) (roundKey w (k + 1)) := by
  simp only [rnds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem cipher_eq (nr : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher nr w x = addRoundKey (shiftRows (subBytes (rnds w x (nr - 1)))) (roundKey w nr) := rfl

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem roundKey_getD (m : Mem) (p : Addr) {L j i : Nat} (hi : i < 16) (hj : 16 * j + 16 ≤ L) :
    (roundKey (bytesAt m p L) j).getD i 0 = m (p + BitVec.ofNat 64 (16 * j + i)) := by
  simp [roundKey, bytesAt, List.getD, hi, show 16 * j + i < L by omega]

/-- Round key `j`, loaded from the schedule. -/
theorem byte_roundKey (m : Mem) (p : Addr) {L j : Nat} (hj : 16 * j + 16 ≤ L) :
    ∀ i < 16, byte (m.readW (p + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 128) i =
      (roundKey (bytesAt m p L) j).getD i 0 := by
  intro i hi
  rw [VG.Proof.Gcm.X86_64.byte_readW _ _ hi, roundKey_getD _ _ hi hj, ofInt_natCast,
    BitVec.add_assoc, BitVec.ofNat_add]

theorem st_toList (r : BitVec 128) : (st r).toList = (List.range 16).map (byte r) := by
  apply List.ext_getElem <;> simp [st]

/-- `CIPH_K` of a block, as `Spec.Gcm.aesWith` states it, from the register
`r` that encrypting the block's bytes left. -/
theorem aesWith_eq (nr : Nat) (w : List Byte) (x r : BitVec 128)
    (h : st r = cipher nr w (st (XBinOp.eval .pshufb x VG.Proof.Gcm.X86_64.revMask))) :
    Spec.Gcm.aesWith nr w x = XBinOp.eval .pshufb r VG.Proof.Gcm.X86_64.revMask := by
  have e : (Vector.ofFn fun i => (Spec.Gcm.toBytes x).getD i 0) =
      st (XBinOp.eval .pshufb x VG.Proof.Gcm.X86_64.revMask) := by
    apply st_ext; intro i hi
    rw [getD_ofFn hi, getD_st _ hi, VG.Proof.Gcm.X86_64.byte_pshufb_rev _ hi]
    simp [Spec.Gcm.toBytes, List.getD, hi, byte]
  rw [Spec.Gcm.aesWith, e, ← h, st_toList, VG.Proof.Gcm.X86_64.gcmOfBytes_eq,
    VG.Proof.Gcm.X86_64.pshufb_rev]

end VG.Proof.Aes.X86_64.AesNi

end

/-!
# AES-NI: encrypting the block registers

`aes_ok`: `Impl.Aes.X86_64.AesNi.aes regs` encrypts each register of `regs`
with the key schedule at `rdi` (10, 12 or 14 rounds, as `rsi` says), whatever
the list of registers; the rounds are composed by induction, one symbolic
execution per instruction.
-/

namespace VG.Proof.Aes.X86_64.AesNi

open Spec.Gcm

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for
`vg_aes_ctr32_aesni(schedule: *const [u8; 240], rounds: usize, counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])`:
XORs the AES counter-mode keystream from the counter block at `counter`
into the `n` blocks at `data`, and advances the counter block by `n`.

The code may read `schedule` (240 bytes) and read and write `counter` (16
bytes), `data` (`16 n` bytes) and `scratch` (2048 bytes). These may not
overlap each other, nor the return address on the stack, and `data` may not
wrap around the end of the address space. `rounds` is 10, 12 or 14. The
pointers, `rounds` and `n` are public; the key schedule, the counter block
and the data are secret. -/
def ctr32X86_64 : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let counter : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let scratch : Region := ⟨s.gpr .r9, 2048⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint counter ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    let ciph := aesWith (s.gpr .rsi).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1)))
    blocksAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
        ctr32 ciph (blockAt s.mem (s.gpr .rdx)) (blocksAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) ∧
      blockAt s'.mem (s.gpr .rdx) = Nat.repeat inc32 (s.gpr .r8).toNat (blockAt s.mem (s.gpr .rdx))
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for
`vg_aes_expand_key_aesni(key: *const u8, key_len: usize, schedule: *mut [u8; 240], scratch: *mut [u64; 64])`:
for a key of 16, 24 or 32 bytes at `key`, writes its key schedule
(`16 (Nr + 1)` bytes) to `schedule`.

The code may read `key` (`key_len` bytes) and read and write `schedule`
(240 bytes) and `scratch` (512 bytes), which may not overlap the return
address on the stack. The pointers and `key_len` are public; the key is
secret. -/
def expandKeyX86_64 : Contract X86_64.isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let sched : Region := ⟨s.gpr .rdx, 240⟩
    let scratch : Region := ⟨s.gpr .rcx, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ ret.Disjoint sched ∧
    ((s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) (16 * (Spec.Aes.rounds ((s.gpr .rsi).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx

end VG.Proof.Aes.X86_64.AesNi

namespace VG.Proof.Aes.X86_64.AesNi

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ keyOp round aes)
open VG.Spec.Aes (subBytes shiftRows mixColumns addRoundKey roundKey cipher bytesAt)

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

/-- An address relative to `p + o`, as a distance from `p`. -/
theorem off_toNat (a p : Addr) {o : Nat} (ho : o < 2 ^ 64) :
    (a - (p + BitVec.ofNat 64 o)).toNat = ((a - p).toNat + (2 ^ 64 - o)) % 2 ^ 64 := by
  rw [show a - (p + BitVec.ofNat 64 o) = (a - p) - BitVec.ofNat 64 o by
      simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc],
    BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho, Nat.add_comm]

/-- `s'` is `s` but for the SSE registers `rs` (and the flags). -/
structure XFrame (rs : List XReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem XFrame.refl (rs : List XReg) (s : State) : XFrame rs s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem XFrame.trans {rs : List XReg} {s s' s'' : State} (h : XFrame rs s s') (h' : XFrame rs s' s'') :
    XFrame rs s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.xmm r hr).trans (h.xmm r hr)⟩

theorem XFrame.comp {rs rs' : List XReg} {s s' s'' : State} (h : XFrame rs s s')
    (h' : XFrame rs' s' s'') : XFrame (rs ++ rs') s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, fun r hr => by
    simp only [List.mem_append, not_or] at hr
    exact (h'.xmm r hr.2).trans (h.xmm r hr.1)⟩

theorem XFrame.mono {rs rs' : List XReg} {s s' : State} (h : XFrame rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    XFrame rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

/-- `op b, xmm8` for each `b` of `regs`. -/
theorem map_ok (op : XBinOp) : ∀ (regs : List XReg) (s : State), regs.Nodup → .xmm8 ∉ regs →
    WP isa (.block (regs.map fun b => .xop (.bin op b .xmm8))) s fun s' =>
      (∀ b ∈ regs, s'.xmm b = op.eval (s.xmm b) (s.xmm .xmm8)) ∧ XFrame regs s s'
  | [], s, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, XFrame.refl _ _⟩
  | b :: bs, s, hnd, h8 => by
    have hb8 : b ≠ .xmm8 := fun h => h8 (h ▸ List.mem_cons_self ..)
    have h8' : .xmm8 ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨s.setXmm b (op.eval (s.xmm b) (s.xmm .xmm8)), rfl, ?_⟩
    refine WP.mono (map_ok op bs _ (List.nodup_cons.mp hnd).2 h8') fun s' ⟨hv, hf⟩ => ⟨?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [hf.xmm _ hbs]; simp [State.setXmm]
      · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
        rw [hv c hc]; simp [State.setXmm, hcb, Ne.symm hb8]
    · refine ⟨hf.gpr, hf.mem, hf.rd, hf.wr, fun r hr => ?_⟩
      simp only [List.mem_cons, not_or] at hr
      rw [hf.xmm r hr.2]; simp [State.setXmm, hr.1]

/-- A round key into `xmm8`, then `op b, xmm8` for each `b` of `regs`. -/
theorem keyOp_ok (regs : List XReg) (op : XBinOp) (a : MemOp) (s : State) (hnd : regs.Nodup)
    (h8 : .xmm8 ∉ regs) (hin : InRegions (s.rd ++ s.wr) (s.ea a) 16) :
    WP isa (.block (keyOp regs op a)) s fun s' =>
      (∀ b ∈ regs, s'.xmm b = op.eval (s.xmm b) (s.mem.readW (s.ea a) 128)) ∧
      XFrame (.xmm8 :: regs) s s' := by
  rw [keyOp, WP.block_cons_iff]
  refine ⟨s.setXmm .xmm8 (s.mem.readW (s.ea a) 128), by
    simp [isa, exec, State.load128, hin], ?_⟩
  refine WP.mono (map_ok op regs _ hnd h8) fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, ?_⟩
  · have hb8 : b ≠ .xmm8 := fun h => h8 (h ▸ hb)
    rw [hv b hb]; simp [State.setXmm, hb8]
  · refine ⟨hf.gpr, hf.mem, hf.rd, hf.wr, fun r hr => ?_⟩
    simp only [List.mem_cons, not_or] at hr
    rw [hf.xmm r hr.2]; simp [State.setXmm, hr.1]

/-! ## The rounds -/

/-- Each register `b` of `regs` holds the state after `k` rounds of the
cipher, from the state `x b`. -/
def RInv (regs : List XReg) (w : List Byte) (x : XReg → Spec.Aes.State) (k : Nat) (s : State) : Prop :=
  ∀ b ∈ regs, st (s.xmm b) = rnds w (x b) k

/-- What the rounds need of the state: the key schedule at `rdi`, readable. -/
structure Keys (nr : Nat) (w : List Byte) (s : State) : Prop where
  sched : w = bytesAt s.mem (s.gpr .rdi) (16 * (nr + 1))
  le : nr ≤ 14
  keys : ∀ j ≤ nr, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 16

theorem Keys.of_frame {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State} (h : Keys nr w s)
    (hf : XFrame rs s s') : Keys nr w s' :=
  ⟨by rw [hf.mem, hf.gpr]; exact h.sched, h.le, by rw [hf.rd, hf.wr, hf.gpr]; exact h.keys⟩

theorem round_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} {k : Nat} (hk : k + 1 ≤ nr) {s : State}
    (hK : Keys nr w s) (hI : RInv regs w x k s) :
    WP isa (.block (round regs (k + 1))) s fun s' =>
      RInv regs w x (k + 1) s' ∧ XFrame (.xmm8 :: regs) s s' := by
  refine WP.mono (keyOp_ok regs .aesenc _ s hnd h8 (by rw [ea_at]; exact hK.keys _ hk))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, aesenc_st _ _ (roundKey w (k + 1)) (by
    rw [hK.sched, ea_at]; exact byte_roundKey _ _ (by omega)), hI b hb, rnds_succ]

theorem rounds_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} (k : Nat) (s : State) (hk : k ≤ nr)
    (hK : Keys nr w s) (hI : RInv regs w x 0 s) :
    WP isa (.block ((List.range k).flatMap fun j => round regs (j + 1))) s fun s' =>
      RInv regs w x k s' ∧ XFrame (.xmm8 :: regs) s s' := by
  induction k with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, XFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (round_ok regs hnd h8 (k := k) (by omega) (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

/-- `cmp rsi, c` with `rsi = nr`. -/
theorem cmpRsi_ok (s : State) (c : BitVec 32) (nr : Nat) (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr) :
    WP isa (.block [.alu .cmp .rsi (.imm c)]) s fun s' =>
      s'.zf = some (BitVec.ofNat 64 nr - c.signExtend 64 == 0) ∧ XFrame [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, hrsi, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem aes_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (s : State) (hK : Keys nr w s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (aes regs) s fun s' =>
      (∀ b ∈ regs, st (s'.xmm b) = cipher nr w (st (s.xmm b))) ∧ XFrame (.xmm8 :: regs) s s' := by
  let x : XReg → Spec.Aes.State := fun b => st (s.xmm b)
  have k0 := byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := 0) (by omega)
  simp only [Nat.mul_zero] at k0
  -- `AddRoundKey` and rounds 1–9.
  have h₁ : WP isa (.block (keyOp regs .pxor (at_ .rdi 0) ++
      (List.range 9).flatMap fun j => round regs (j + 1))) s fun s' =>
      RInv regs w x 9 s' ∧ XFrame (.xmm8 :: regs) s s' := by
    rw [WP.block_append_iff]
    refine WP.mono (keyOp_ok regs .pxor _ s hnd h8 (by rw [ea_at]; exact hK.keys 0 (by omega)))
      fun s₁ ⟨hv₁, hf₁⟩ => ?_
    have hI₁ : RInv regs w x 0 s₁ := fun b hb => by
      rw [hv₁ b hb, pxor_st _ _ (roundKey w 0) (by rw [hK.sched, ea_at]; exact k0), rnds_zero]
    exact WP.mono (rounds_ok regs hnd h8 9 s₁ (by omega) (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩
  -- Rounds 10 to `nr - 1`.
  have h₂ : ∀ s₁, RInv regs w x 9 s₁ → XFrame (.xmm8 :: regs) s s₁ →
      s₁.zf = some (BitVec.ofNat 64 nr - (10 : BitVec 32).signExtend 64 == 0) →
      WP isa (.ite .e (.block [])
        (.seq (.block (round regs 10 ++ round regs 11 ++ [.alu .cmp .rsi (.imm 12)]))
          (.ite .e (.block []) (.block (round regs 12 ++ round regs 13))))) s₁ fun s' =>
        RInv regs w x (nr - 1) s' ∧ XFrame (.xmm8 :: regs) s s' := by
    intro s₁ hI₁ hf₁ hz₁
    have hK₁ := hK.of_frame hf₁
    have hrsi₁ : s₁.gpr .rsi = BitVec.ofNat 64 nr := by rw [hf₁.gpr, hrsi]
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [eval, hz₁]) (fun _ => WP.block_nil ⟨hI₁, hf₁⟩)
        (fun h => absurd h (by decide))
    all_goals
      refine WP.ite false (by simp [eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq ?_
      rw [WP.block_append_iff, WP.block_append_iff]
      refine WP.mono (round_ok regs hnd h8 (k := 9) (by omega) hK₁ hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_
      refine WP.mono (round_ok regs hnd h8 (k := 10) (by omega) (hK₁.of_frame hf₂) hI₂)
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      have hrsi₃ : s₃.gpr .rsi = s₁.gpr .rsi := by rw [hf₃.gpr, hf₂.gpr]
      refine WP.mono (cmpRsi_ok s₃ 12 _ (hrsi₃.trans hrsi₁)) fun s₄ ⟨hz₄, hf₄⟩ => ?_
      have hf₁₄ := hf₁.trans (hf₂.trans (hf₃.trans (hf₄.mono (by simp))))
    · exact WP.ite true (by simp [eval, hz₄]) (fun _ => WP.block_nil
        ⟨fun b hb => by rw [hf₄.xmm b (by simp)]; exact hI₃ b hb, hf₁₄⟩)
        (fun h => absurd h (by decide))
    · refine WP.ite false (by simp [eval, hz₄]) (fun h => absurd h (by decide)) fun _ => ?_
      rw [WP.block_append_iff]
      have hK₄ := hK₁.of_frame (hf₂.trans (hf₃.trans (hf₄.mono (by simp))))
      have hI₄ : RInv regs w x 11 s₄ := fun b hb => by rw [hf₄.xmm b (by simp)]; exact hI₃ b hb
      refine WP.mono (round_ok regs hnd h8 (k := 11) (by omega) hK₄ hI₄) fun s₅ ⟨hI₅, hf₅⟩ => ?_
      exact WP.mono (round_ok regs hnd h8 (k := 12) (by omega) (hK₄.of_frame hf₅) hI₅)
        fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁₄.trans (hf₅.trans hf')⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono h₁ fun s₁ ⟨hI₁, hf₁⟩ => ?_
  refine WP.mono (cmpRsi_ok s₁ 10 nr (by rw [hf₁.gpr, hrsi])) fun s₁' ⟨hz₁, hf₁'⟩ => ?_
  have hf₁₁ := hf₁.trans (hf₁'.mono (by simp))
  refine WP.seq (WP.mono (h₂ s₁' (fun b hb => by rw [hf₁'.xmm b (by simp)]; exact hI₁ b hb) hf₁₁ hz₁)
    fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  have hea : s₂.ea (at_ .r10 0) = s₂.gpr .rdi + BitVec.ofInt 64 ((16 * nr : Nat) : Int) := by
    rw [ea_at, hf₂.gpr, hr10, ofInt_natCast, ofInt_natCast]; exact BitVec.add_zero _
  have hK₂ := hK.of_frame hf₂
  refine WP.mono (keyOp_ok regs .aesenclast _ s₂ hnd h8 (by rw [hea]; exact hK₂.keys nr (Nat.le_refl _)))
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb => ?_, hf₂.trans hf'⟩
  rw [hv b hb, aesenclast_st _ _ (roundKey w nr) (by
    rw [hea, hK₂.sched]; exact byte_roundKey _ _ (by omega)), hI₂ b hb, cipher_eq]
