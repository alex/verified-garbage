import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Aes.AArch64.Aese
import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.TCB.AArch64.Target

/-!
# The Armv8 AES instructions are FIPS 197's rounds

A vector register holds an AES state as its 16 bytes in memory order (`st`):
byte `r + 4c` is `s[r, c]`, as FIPS 197 §3.4 lays the state out and as the Arm
ARM's AES instructions read it. On such registers `eor` is `AddRoundKey`
(`eor_st`), `aese` is `AddRoundKey`, `SubBytes` and `ShiftRows` (`aese_st`),
and `aesmc` is `MixColumns` (`aesmc_st`); the S-box of the ISA model, computed
by repeated squaring, is the one of `Spec/Aes.lean` (`sbox_eq`).

`aes_ok`: `Impl.Aes.AArch64.Aese.aes regs` encrypts each register of `regs`
with the round keys in `v16`–`v30`, whatever the list of registers.
-/

namespace VG.Proof.Aes.AArch64.Aese

open VG.AArch64
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

/-! ## Bytes of vectors -/

/-- Bit `r` of block `k` of `x ++ y`, blocks being `n` bits wide. -/
theorem getLsbD_append_block {w n : Nat} (x : BitVec w) (y : BitVec n) (k : Nat) {r : Nat} (hr : r < n) :
    (x ++ y).getLsbD (n * k + r) = if k = 0 then y.getLsbD r else x.getLsbD (n * (k - 1) + r) := by
  rw [BitVec.getLsbD_append]
  by_cases hk : k = 0
  · subst hk; simp [hr]
  · have h : n ≤ n * k := Nat.le_mul_of_pos_right n (by omega)
    simp only [hk, show ¬ n * k + r < n by omega, ↓reduceIte]
    exact congrArg _ (by rw [Nat.mul_sub_one, Nat.sub_add_comm h])

theorem getLsbD_ofVBytes (f : Nat → BitVec 8) {k r : Nat} (hk : k < 16) (hr : r < 8) :
    (ofVBytes f).getLsbD (8 * k + r) = (f k).getLsbD r := by
  simp only [ofVBytes, getLsbD_append_block _ _ _ hr]
  match k, hk with
  | 0, _ => ?_
  | 1, _ => ?_
  | 2, _ => ?_
  | 3, _ => ?_
  | 4, _ => ?_
  | 5, _ => ?_
  | 6, _ => ?_
  | 7, _ => ?_
  | 8, _ => ?_
  | 9, _ => ?_
  | 10, _ => ?_
  | 11, _ => ?_
  | 12, _ => ?_
  | 13, _ => ?_
  | 14, _ => ?_
  | 15, _ => ?_
  | _ + 16, h => exact absurd h (by omega)
  all_goals
    simp only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add]

theorem vbyte_ofVBytes (f : Nat → BitVec 8) {i : Nat} (hi : i < 16) : vbyte (ofVBytes f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]
  exact getLsbD_ofVBytes f hi hr

theorem ext_vbyte {a b : BitVec 128} (h : ∀ i < 16, vbyte a i = vbyte b i) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have := congrArg (BitVec.getLsbD · (j % 8)) (h (j / 8) (by omega))
  simp only [vbyte, BitVec.getLsbD_extractLsb', decide_eq_true (Nat.mod_lt j (by omega : 8 > 0)),
    Bool.true_and] at this
  rwa [show 8 * (j / 8) + j % 8 = j by omega] at this

theorem vbyte_readW (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    vbyte (m.readW p 128) i = m (p + BitVec.ofNat 64 i) := by
  rw [← Mem.extractLsb'_read m p (n := 16) hi]
  simp only [vbyte, Mem.readW]
  rfl

theorem vbyte_xor (a b : BitVec 128) (i : Nat) : vbyte (a ^^^ b) i = vbyte a i ^^^ vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hj, decide_true, Bool.true_and]

/-! ## States in registers -/

/-- The AES state held by a register. -/
def st (v : BitVec 128) : Spec.Aes.State := Vector.ofFn fun i => vbyte v i

theorem getD_ofFn {f : Fin 16 → Byte} {i : Nat} (h : i < 16) :
    (Vector.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  simp [Vector.getD, h]

theorem getD_st (v : BitVec 128) {i : Nat} (h : i < 16) : (st v).getD i 0 = vbyte v i := by
  rw [st, getD_ofFn h]

theorem st_ext {s t : Spec.Aes.State} (h : ∀ i < 16, s.getD i 0 = t.getD i 0) : s = t := by
  apply Vector.ext; intro i hi
  have := h i hi
  simpa [Vector.getD, hi] using this

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

theorem vbyte_mapBytes (f : BitVec 8 → BitVec 8) (x : BitVec 128) {i : Nat} (h : i < 16) :
    vbyte (aesMapBytes f x) i = f (vbyte x i) := by
  rw [aesMapBytes, vbyte_ofVBytes _ h]

theorem vbyte_shiftRows (x : BitVec 128) {i : Nat} (h : i < 16) :
    vbyte (aesShiftRows x) i = vbyte x (i % 4 + 4 * ((i / 4 + i % 4) % 4)) := by
  rw [aesShiftRows, vbyte_ofVBytes _ h]

theorem vbyte_mixColumns (x : BitVec 128) {i : Nat} (h : i < 16) :
    vbyte (aesMixColumns x) i =
      aesMul 0x02 (vbyte x ((i % 4 + 0) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x03 (vbyte x ((i % 4 + 1) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (vbyte x ((i % 4 + 2) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (vbyte x ((i % 4 + 3) % 4 + 4 * (i / 4))) := by
  rw [aesMixColumns, aesMixWith, vbyte_ofVBytes _ h]

/-! ## The instructions -/

/-- A round key in a register: its bytes are those of `rk`. -/
def KeyIs (k : BitVec 128) (rk : List Byte) : Prop := ∀ i < 16, vbyte k i = rk.getD i 0

/-- `eor` with a round key is `AddRoundKey`. -/
theorem eor_st {v k : BitVec 128} {rk : List Byte} (hk : KeyIs k rk) :
    st (v ^^^ k) = addRoundKey (st v) rk := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, getD_addRoundKey _ _ hi, getD_st _ hi, ← hk i hi]
  exact vbyte_xor v k i

/-- `aese` with a round key is `AddRoundKey`, then `SubBytes` and `ShiftRows`. -/
theorem aese_st {v k : BitVec 128} {rk : List Byte} (hk : KeyIs k rk) :
    st (aesMapBytes aesSbox (aesShiftRows (v ^^^ k))) = shiftRows (subBytes (addRoundKey (st v) rk)) := by
  apply st_ext; intro i hi
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + j % 4) % 4) < 16 := fun j => by omega
  rw [getD_st _ hi, getD_shiftRows _ hi, getD_subBytes _ (hs _), getD_addRoundKey _ _ (hs _),
    getD_st _ (hs _), ← hk _ (hs _), vbyte_mapBytes _ _ hi, vbyte_shiftRows _ hi, vbyte_xor, sbox_eq]

/-- `aesmc` is `MixColumns`. -/
theorem aesmc_st (v : BitVec 128) : st (aesMixColumns v) = mixColumns (st v) := by
  apply st_ext; intro i hi
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  rw [getD_st _ hi, getD_mixColumns _ hi, vbyte_mixColumns _ hi]
  simp only [getD_st _ (hr _), mul_eq, mul_one']

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

/-- A full round: `aese` with round key `j`, then `aesmc`. The register
holds the state before the `AddRoundKey` of round key `j`. -/
theorem round_st {v k : BitVec 128} {w : List Byte} {x : Spec.Aes.State} {j : Nat}
    (hk : KeyIs k (roundKey w j)) (h : addRoundKey (st v) (roundKey w j) = rnds w x j) :
    addRoundKey (st (aesMixColumns (aesMapBytes aesSbox (aesShiftRows (v ^^^ k))))) (roundKey w (j + 1)) =
      rnds w x (j + 1) := by
  rw [rnds_succ, aesmc_st, aese_st hk, h]

/-- The last round: `aese` with round key `Nr − 1`, then `eor` with round key `Nr`. -/
theorem last_st {v k k' : BitVec 128} {w : List Byte} {x : Spec.Aes.State} {nr : Nat}
    (hk : KeyIs k (roundKey w (nr - 1))) (hk' : KeyIs k' (roundKey w nr))
    (h : addRoundKey (st v) (roundKey w (nr - 1)) = rnds w x (nr - 1)) :
    st (aesMapBytes aesSbox (aesShiftRows (v ^^^ k)) ^^^ k') = cipher nr w x := by
  rw [eor_st hk', aese_st hk, h, cipher_eq]

/-- Round key `j`, loaded from the schedule. -/
theorem keyIs_readW (m : Mem) (p : Addr) {L j : Nat} (hj : 16 * j + 16 ≤ L) :
    KeyIs (m.readW (p + BitVec.ofNat 64 (16 * j)) 128) (roundKey (bytesAt m p L) j) := by
  intro i hi
  rw [vbyte_readW _ _ hi, BitVec.add_assoc, ← BitVec.ofNat_add]
  simp [roundKey, bytesAt, List.getD, hi, show 16 * j + i < L by omega]

end VG.Proof.Aes.AArch64.Aese

/-!
## Encrypting the block registers
-/

namespace VG.Proof.Aes.AArch64.Aese

open VG VG.AArch64
open VG.Impl.Aes.AArch64.Aese (kreg rnd last aes)
open VG.Spec.Aes (roundKey cipher addRoundKey)

/-- `s'` is `s` but for the vector registers `rs`. -/
structure VFrame (rs : List VReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  sp : s'.sp = s.sp
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  v : ∀ r, r ∉ rs → s'.v r = s.v r

theorem VFrame.refl (rs : List VReg) (s : State) : VFrame rs s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem VFrame.trans {rs : List VReg} {s s' s'' : State} (h : VFrame rs s s') (h' : VFrame rs s' s'') :
    VFrame rs s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.sp.trans h.sp, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.v r hr).trans (h.v r hr)⟩

theorem VFrame.mono {rs rs' : List VReg} {s s' : State} (h : VFrame rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VFrame rs' s s' :=
  ⟨h.gpr, h.sp, h.mem, h.rd, h.wr, fun r hr => h.v r fun h' => hr (hs r h')⟩

/-- Two instructions that set `b` to `g (b) (k)`, for each register `b` of `regs`. -/
theorem each_ok (f : VReg → List Instr) (g : BitVec 128 → BitVec 128 → BitVec 128) (k : VReg)
    (hf : ∀ b s, b ≠ k → runBlock isa (f b) s = some (s.setV b (g (s.v b) (s.v k)))) :
    ∀ (regs : List VReg) (s : State), regs.Nodup → k ∉ regs →
    WP isa (.block (regs.flatMap f)) s fun s' =>
      (∀ b ∈ regs, s'.v b = g (s.v b) (s.v k)) ∧ VFrame regs s s'
  | [], s, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, VFrame.refl _ _⟩
  | b :: bs, s, hnd, hk => by
    have hbk : b ≠ k := fun h => hk (h ▸ List.mem_cons_self ..)
    have hk' : k ∉ bs := fun h => hk (List.mem_cons_of_mem _ h)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.of_runBlock ⟨_, hf b s hbk, ?_⟩
    refine WP.mono (each_ok f g k hf bs _ (List.nodup_cons.mp hnd).2 hk') fun s' ⟨hv, hfr⟩ => ⟨?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [hfr.v _ hbs]; simp [State.setV]
      · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
        rw [hv c hc]; simp [State.setV, hcb, Ne.symm hbk]
    · refine ⟨hfr.gpr, hfr.sp, hfr.mem, hfr.rd, hfr.wr, fun r hr => ?_⟩
      simp only [List.mem_cons, not_or] at hr
      rw [hfr.v r hr.2]; simp [State.setV, hr.1]

theorem setV_v_self (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).v r = x := by
  simp [State.setV]

theorem setV_v_of_ne (s : State) {r r' : VReg} (x : BitVec 128) (h : r' ≠ r) :
    (s.setV r x).v r' = s.v r' := by
  simp [State.setV, h]

theorem setV_setV (s : State) (r : VReg) (x y : BitVec 128) : (s.setV r x).setV r y = s.setV r y := by
  simp only [State.setV]
  congr 1
  funext r'
  split <;> rfl

theorem rnd_run (k b : VReg) (s : State) :
    runBlock isa [.vop (.aese b k), .vop (.aesmc b b)] s =
      some (s.setV b (aesMixColumns (aesMapBytes aesSbox (aesShiftRows (s.v b ^^^ s.v k))))) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]
  rw [setV_v_self, setV_setV]

theorem last_run (b : VReg) (s : State) (hb30 : b ≠ .v30) :
    runBlock isa [.vop (.aese b .v29), .vop (.logic .eor b b .v30)] s =
      some (s.setV b (aesMapBytes aesSbox (aesShiftRows (s.v b ^^^ s.v .v29)) ^^^ s.v .v30)) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]
  rw [setV_v_self, setV_v_of_ne _ _ (Ne.symm hb30), setV_setV]

/-- The registers the blocks may be in. -/
def BlockRegs (regs : List VReg) : Prop :=
  regs.Nodup ∧ ∀ r ∈ regs, r ≠ .v16 ∧ r ≠ .v17 ∧ r ≠ .v18 ∧ r ≠ .v19 ∧ r ≠ .v20 ∧ r ≠ .v21 ∧
    r ≠ .v22 ∧ r ≠ .v23 ∧ r ≠ .v24 ∧ r ≠ .v25 ∧ r ≠ .v26 ∧ r ≠ .v27 ∧ r ≠ .v28 ∧ r ≠ .v29 ∧
    r ≠ .v30

theorem BlockRegs.kreg {regs : List VReg} (h : BlockRegs regs) (j : Nat) : kreg j ∉ regs := by
  intro hj
  have := (h.2 _ hj)
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | _ + 12 => simp [Impl.Aes.AArch64.Aese.kreg] at this

/-- Each register `b` of `regs` holds the state before the `AddRoundKey` of
round key `j`, from the state `x b`. -/
def RInv (regs : List VReg) (w : List Byte) (x : VReg → Spec.Aes.State) (j : Nat) (s : State) : Prop :=
  ∀ b ∈ regs, addRoundKey (st (s.v b)) (roundKey w j) = rnds w (x b) j

/-- What the rounds need of the state: the round keys in `v16`–`v30`, and
`x6`, `x7` for the number of rounds. -/
structure Keys (nr : Nat) (w : List Byte) (s : State) : Prop where
  rounds : nr = 10 ∨ nr = 12 ∨ nr = 14
  full : ∀ j, j + 2 ≤ nr → KeyIs (s.v (kreg j)) (roundKey w j)
  k29 : KeyIs (s.v .v29) (roundKey w (nr - 1))
  k30 : KeyIs (s.v .v30) (roundKey w nr)
  x6 : s.gpr .x6 = BitVec.ofNat 64 nr - 10
  x7 : s.gpr .x7 = BitVec.ofNat 64 nr - 12

theorem Keys.of_frame {nr : Nat} {w : List Byte} {rs : List VReg} {s s' : State} (h : Keys nr w s)
    (hf : VFrame rs s s') (hrs : BlockRegs rs) : Keys nr w s' :=
  ⟨h.rounds, fun j hj => by rw [hf.v _ (hrs.kreg j)]; exact h.full j hj,
    by rw [hf.v _ fun h' => (hrs.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl]; exact h.k29,
    by rw [hf.v _ fun h' => (hrs.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.2 rfl]; exact h.k30,
    by rw [hf.gpr]; exact h.x6, by rw [hf.gpr]; exact h.x7⟩

theorem round_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {j : Nat} (hj : j + 2 ≤ nr) {s : State} (hK : Keys nr w s)
    (hI : RInv regs w x j s) :
    WP isa (.block (rnd regs (kreg j))) s fun s' => RInv regs w x (j + 1) s' ∧ VFrame regs s s' := by
  refine WP.mono (each_ok _ (fun v k => aesMixColumns (aesMapBytes aesSbox (aesShiftRows (v ^^^ k))))
    (kreg j) (fun b s _ => rnd_run _ b s) regs s hr.1 (hr.kreg j))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb]
  exact round_st (hK.full j hj) (hI b hb)

theorem rounds_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : Keys nr w s) (hI : RInv regs w x 0 s) :
    ∀ k, k + 1 ≤ nr →
    WP isa (.block ((List.range k).flatMap fun i => rnd regs (kreg i))) s fun s' =>
      RInv regs w x k s' ∧ VFrame regs s s'
  | 0, _ => by
    rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, VFrame.refl _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (rounds_ok hr hK hI k (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (round_ok hr (j := k) (by omega) (hK.of_frame hf₁ hr) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

theorem last_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : Keys nr w s) (hI : RInv regs w x (nr - 1) s) :
    WP isa (.block (last regs)) s fun s' =>
      (∀ b ∈ regs, st (s'.v b) = cipher nr w (x b)) ∧ VFrame regs s s' := by
  have h29 : .v29 ∉ regs := fun h' => (hr.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl
  have h30 : ∀ b ∈ regs, b ≠ .v30 := fun b h' => (hr.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.2
  -- `last` is `each_ok` for `v29`, with `v30` read by each step (and not written).
  have e : ∀ (rs : List VReg) (s : State), rs.Nodup → .v29 ∉ rs → (∀ b ∈ rs, b ≠ .v30) →
      WP isa (.block (last rs)) s fun s' =>
        (∀ b ∈ rs, s'.v b = aesMapBytes aesSbox (aesShiftRows (s.v b ^^^ s.v .v29)) ^^^ s.v .v30) ∧
        VFrame rs s s' := by
    intro rs
    induction rs with
    | nil => intro s _ _ _; exact WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, VFrame.refl _ _⟩
    | cons b bs ih =>
      intro s hnd hk h30'
      have hb29 : b ≠ .v29 := fun h => hk (h ▸ List.mem_cons_self ..)
      have hb30 : b ≠ .v30 := h30' b List.mem_cons_self
      have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
      rw [Impl.Aes.AArch64.Aese.last, List.flatMap_cons, WP.block_append_iff]
      refine WP.of_runBlock ⟨_, last_run b s hb30, ?_⟩
      refine WP.mono (ih _ (List.nodup_cons.mp hnd).2 (fun h => hk (List.mem_cons_of_mem _ h))
        (fun c hc => h30' c (List.mem_cons_of_mem _ hc))) fun s' ⟨hv, hfr⟩ => ⟨?_, ?_⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · rw [hfr.v _ hbs]; simp [State.setV]
        · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
          rw [hv c hc]; simp [State.setV, hcb, Ne.symm hb29, Ne.symm hb30]
      · refine ⟨hfr.gpr, hfr.sp, hfr.mem, hfr.rd, hfr.wr, fun r hr => ?_⟩
        simp only [List.mem_cons, not_or] at hr
        rw [hfr.v r hr.2]; simp [State.setV, hr.1]
  refine WP.mono (e regs s hr.1 h29 h30) fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb]
  exact last_st hK.k29 hK.k30 (hI b hb)

/-- Two full rounds, with round keys `j` and `j + 1`. -/
theorem two_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (j : Nat) {k₁ k₂ : VReg} (e₁ : k₁ = kreg j)
    (e₂ : k₂ = kreg (j + 1)) (hj : j + 3 ≤ nr) (hK : Keys nr w s) (hI : RInv regs w x j s) :
    WP isa (.block (rnd regs k₁ ++ rnd regs k₂)) s fun s' =>
      RInv regs w x (j + 2) s' ∧ VFrame regs s s' := by
  subst e₁ e₂
  rw [WP.block_append_iff]
  refine WP.mono (round_ok hr (by omega) hK hI) fun s₁ ⟨hI₁, hf₁⟩ => ?_
  exact WP.mono (round_ok hr (by omega) (hK.of_frame hf₁ hr) hI₁)
    fun s₂ ⟨hI₂, hf₂⟩ => ⟨hI₂, hf₁.trans hf₂⟩

/-- The full rounds with round keys `9 … Nr − 2`. -/
theorem mid_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : Keys nr w s) (hI : RInv regs w x 9 s) :
    WP isa (.ite (.zero .x .x6) (.block [])
        (.seq (.block (rnd regs .v25 ++ rnd regs .v26))
          (.ite (.zero .x .x7) (.block []) (.block (rnd regs .v27 ++ rnd regs .v28))))) s
      fun s' => RInv regs w x (nr - 1) s' ∧ VFrame regs s s' := by
  have hx6 := hK.x6
  obtain rfl | rfl | rfl := hK.rounds
  · exact WP.ite true (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun _ => WP.block_nil ⟨hI, VFrame.refl _ _⟩) (fun h => absurd h (by decide))
  · refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq (WP.mono (two_ok hr 9 rfl rfl (by omega) hK hI) fun s₃ ⟨hI₃, hf₃⟩ => ?_)
    have hx7 : s₃.gpr .x7 = BitVec.ofNat 64 12 - 12 := by rw [hf₃.gpr]; exact hK.x7
    exact WP.ite true (by simp only [AArch64.eval, State.read, hx7]; decide)
      (fun _ => WP.block_nil ⟨hI₃, hf₃⟩) (fun h => absurd h (by decide))
  · refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq (WP.mono (two_ok hr 9 rfl rfl (by omega) hK hI) fun s₃ ⟨hI₃, hf₃⟩ => ?_)
    have hx7 : s₃.gpr .x7 = BitVec.ofNat 64 14 - 12 := by rw [hf₃.gpr]; exact hK.x7
    refine WP.ite false (by simp only [AArch64.eval, State.read, hx7]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    exact WP.mono (two_ok hr 11 rfl rfl (by omega) (hK.of_frame hf₃ hr) hI₃)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans hf'⟩

theorem aes_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte} {s : State}
    (hK : Keys nr w s) :
    WP isa (aes regs) s fun s' =>
      (∀ b ∈ regs, st (s'.v b) = cipher nr w (st (s.v b))) ∧ VFrame regs s s' := by
  have hI₀ : RInv regs w (fun b => st (s.v b)) 0 s := fun b _ => (rnds_zero w _).symm
  refine WP.seq (WP.mono (rounds_ok hr hK hI₀ 9 (by have := hK.rounds; omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (mid_ok hr (hK.of_frame hf₁ hr) hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  exact WP.mono (last_ok hr (hK.of_frame (hf₁.trans hf₂) hr) hI₂)
    fun s' ⟨hv, hf'⟩ => ⟨hv, hf₁.trans (hf₂.trans hf')⟩

end VG.Proof.Aes.AArch64.Aese
