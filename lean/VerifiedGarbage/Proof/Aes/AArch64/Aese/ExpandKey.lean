import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
import VerifiedGarbage.Proof.Aes.AArch64.ExpandKey
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Range

/-!
# AES key expansion with the Armv8 Cryptographic Extension

Untrusted: everything here is checked by Lean. `expandKey_verified` proves
`Impl.Aes.AArch64.Aese.expandKey` against `Proof.Aes.expandKeyAArch64` (the
contract `vg_aes_expand_key` is proven against), and so against the shared
contract.

`W m kp nk i` is word `w[i]` of the key schedule of the `nk`-word key at
`kp`, as the 32-bit value whose bytes, least significant first, are the
word's bytes (`wv`), which is how a `w` register holds it. `expandKey_eq`:
FIPS 197's `KEYEXPANSION` is these words, in order; `bytesAt_eq`: memory
holding them as little-endian words holds the schedule. `word_ok`: each
word's code, for any index, computes and stores the next word; the words
are composed by induction (`wp_range_flatMap`).
-/

namespace VG.Proof.Aes.AArch64.Aese

open VG VG.AArch64
open VG.Spec.Aes (Word subWord rotWord rcon xorWord expandWords expandKey bytesAt rounds)
open VG.Impl.Aes.AArch64.Aese (rc wregs wreg subW word expandN)

/-! ## Words -/

/-- The bytes of a word, least significant first. -/
def wv (d : BitVec 32) : Word := (List.range 4).map fun j => d.extractLsb' (8 * j) 8

/-- `SUBWORD`, on a word as a register holds it. -/
def sub32 (x : BitVec 32) : BitVec 32 :=
  aesSbox (x.extractLsb' 24 8) ++ aesSbox (x.extractLsb' 16 8) ++
    aesSbox (x.extractLsb' 8 8) ++ aesSbox (x.extractLsb' 0 8)

/-- `temp` of `KEYEXPANSION` for word `i`, from `w[i − 1]`. -/
def temp32 (nk i : Nat) (x : BitVec 32) : BitVec 32 :=
  if i % nk = 0 then (sub32 x).rotateRight 8 ^^^ (rc (i / nk)).setWidth 32
  else if nk > 6 ∧ i % nk = 4 then sub32 x else x

/-- Word `i` of the key schedule of the `nk`-word key at `kp`. -/
def W (m : Mem) (kp : Addr) (nk : Nat) (i : Nat) : BitVec 32 :=
  if i < nk ∨ nk = 0 then m.readW (kp + BitVec.ofNat 64 (4 * i)) 32
  else W m kp nk (i - nk) ^^^ temp32 nk i (W m kp nk (i - 1))
termination_by i
decreasing_by all_goals omega

theorem W_lt {m : Mem} {kp : Addr} {nk i : Nat} (h : i < nk) :
    W m kp nk i = m.readW (kp + BitVec.ofNat 64 (4 * i)) 32 := by
  rw [W]; simp [h]

theorem W_ge {m : Mem} {kp : Addr} {nk i : Nat} (h0 : 0 < nk) (h : nk ≤ i) :
    W m kp nk i = W m kp nk (i - nk) ^^^ temp32 nk i (W m kp nk (i - 1)) := by
  rw [W]; simp only [show ¬ (i < nk ∨ nk = 0) by omega, ite_false]

theorem wv_eq (d : BitVec 32) :
    wv d = [d.extractLsb' 0 8, d.extractLsb' 8 8, d.extractLsb' 16 8, d.extractLsb' 24 8] := rfl

theorem extract_xor (a b : BitVec 32) (k : Nat) :
    (a ^^^ b).extractLsb' k 8 = a.extractLsb' k 8 ^^^ b.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem wv_xor (a b : BitVec 32) : wv (a ^^^ b) = xorWord (wv a) (wv b) := by
  simp only [wv_eq, extract_xor, xorWord, List.zipWith_cons_cons, List.zipWith_nil_left]

theorem extract_cat (a b c d : BitVec 8) :
    (a ++ b ++ c ++ d).extractLsb' 0 8 = d ∧ (a ++ b ++ c ++ d).extractLsb' 8 8 = c ∧
      (a ++ b ++ c ++ d).extractLsb' 16 8 = b ∧ (a ++ b ++ c ++ d).extractLsb' 24 8 = a := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp (disch := omega) only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true,
      Bool.true_and, ite_eq_left, ite_eq_right] <;>
    exact congrArg _ (by omega)

theorem rot_cat (a b c d : BitVec 8) : (a ++ b ++ c ++ d).rotateRight 8 = d ++ a ++ b ++ c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi' : i < 32 := hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_append, hi', decide_true, Bool.true_and]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i) with h | h | h | h <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right] <;>
    exact congrArg _ (by omega)

theorem wv_cat (a b c d : BitVec 8) : wv (a ++ b ++ c ++ d) = [d, c, b, a] := by
  obtain ⟨e0, e1, e2, e3⟩ := extract_cat a b c d
  rw [wv_eq, e0, e1, e2, e3]

theorem sub_wv (x : BitVec 32) : subWord (wv x) = wv (sub32 x) := by
  rw [sub32, wv_cat, wv_eq, subWord, sbox_eq]; rfl

theorem subRot_wv (x : BitVec 32) : subWord (rotWord (wv x)) = wv ((sub32 x).rotateRight 8) := by
  rw [sub32, rot_cat, wv_cat, wv_eq, rotWord, subWord, sbox_eq]; rfl

theorem rcon_wv (j : Nat) : rcon j = wv ((rc j).setWidth 32) := by
  rw [show (rc j).setWidth 32 = 0#8 ++ 0#8 ++ 0#8 ++ rc j by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_zero]
    by_cases h : i < 8
    · simp [h]; omega
    · simp [h]; exact fun _ => BitVec.getLsbD_of_ge _ _ (by omega), wv_cat]
  rfl

theorem temp_wv (nk i : Nat) (x : BitVec 32) :
    (if i % nk = 0 then xorWord (subWord (rotWord (wv x))) (rcon (i / nk))
      else if nk > 6 ∧ i % nk = 4 then subWord (wv x) else wv x) = wv (temp32 nk i x) := by
  unfold temp32
  by_cases h1 : i % nk = 0
  · simp only [h1, ite_true, wv_xor, subRot_wv, rcon_wv]
  · by_cases h2 : nk > 6 ∧ i % nk = 4
    · have h2' : (nk > 6 ∧ i % nk = 4) = True := eq_true h2
      simp only [h1, h2', ite_true, ite_false, sub_wv]
    · simp only [h1, h2, ite_false]

/-! ## The key and the schedule -/

theorem getD_mapRange {α : Type} (f : Nat → α) {n i : Nat} (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD, h]

theorem ofNat_add' (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 (a + b) = p + BitVec.ofNat 64 a + BitVec.ofNat 64 b := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- Word `i` of the key. -/
theorem keyWord (m : Mem) (kp : Addr) {L i : Nat} (h : 4 * i + 4 ≤ L) :
    ((bytesAt m kp L).drop (4 * i)).take 4 = wv (m.readW (kp + BitVec.ofNat 64 (4 * i)) 32) := by
  apply List.ext_getElem
  · simp [bytesAt, wv]; omega
  · intro j h₁ h₂
    have hj : j < 4 := by simpa [wv] using h₂
    simp only [List.getElem_take, List.getElem_drop, bytesAt, List.getElem_map, List.getElem_range,
      wv]
    rw [ofNat_add', Mem.readW_byte m (kp + BitVec.ofNat 64 (4 * i)) hj]

theorem expandWords_eq (m : Mem) (kp : Addr) {nk : Nat} (h0 : 0 < nk) :
    ∀ n, expandWords (bytesAt m kp (4 * nk)) nk n = (List.range n).map fun i => wv (W m kp nk i)
  | 0 => rfl
  | i + 1 => by
    rw [expandWords, expandWords_eq m kp h0 i, List.range_succ, List.map_append, List.map_singleton]
    by_cases h : i < nk
    · simp only [h, ite_true]
      rw [keyWord _ _ (by omega), W_lt h]
    · simp only [h, ite_false]
      rw [getD_mapRange _ _ (by omega), getD_mapRange _ _ (by omega), temp_wv, ← wv_xor,
        ← W_ge h0 (by omega)]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-- `KEYEXPANSION`, as words. -/
theorem expandKey_eq (m : Mem) (kp : Addr) {nk : Nat} (h0 : 0 < nk) :
    expandKey (bytesAt m kp (4 * nk)) =
      ((List.range (4 * (rounds nk + 1))).map fun i => wv (W m kp nk i)).flatten := by
  rw [expandKey, length_bytesAt, show 4 * nk / 4 = nk by omega, expandWords_eq m kp h0]

/-- Memory holding the words `f 0 … f (K − 1)` as little-endian words. -/
theorem bytesAt_eq (m : Mem) (p : Addr) (f : Nat → BitVec 32) :
    ∀ K, (∀ i < K, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = f i) →
      bytesAt m p (4 * K) = ((List.range K).map fun i => wv (f i)).flatten
  | 0, _ => rfl
  | K + 1, h => by
    rw [List.range_succ, List.map_append, List.flatten_append, ← bytesAt_eq m p f K
      fun i hi => h i (by omega), List.map_singleton, List.flatten_singleton, ← h K (by omega),
      show 4 * (K + 1) = 4 * K + 4 by omega, bytesAt, bytesAt, List.range_add, List.map_append,
      List.map_map]
    congr 1
    simp only [wv]
    refine List.map_congr_left fun j hj => ?_
    simp only [List.mem_range] at hj
    simp only [Function.comp_apply]
    rw [ofNat_add', Mem.readW_byte m (p + BitVec.ofNat 64 (4 * K)) hj]

/-- Words `0 … K − 1` of `f` are stored at `p`, as little-endian words. -/
def Good (m : Mem) (p : Addr) (f : Nat → BitVec 32) (K : Nat) : Prop :=
  ∀ i < K, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = f i

theorem good_store {m : Mem} {p : Addr} {f : Nat → BitVec 32} {K : Nat} (hG : Good m p f K)
    {v : BitVec 32} (hv : v = f K) (hK : 4 * K + 4 ≤ 240) :
    Good (m.writeW (p + BitVec.ofNat 64 (4 * K)) v) p f (K + 1) := by
  intro i hi
  by_cases h : i < K
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
    exact hG i h
  · rw [show i = K by omega, Mem.readW_writeW_self32, hv]

/-! ## `SubWord` with `aese` -/

theorem vbyte_dup (w : BitVec 32) {k : Nat} (hk : k < 16) :
    vbyte (ofVWords w w w w) k = w.extractLsb' (8 * (k % 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp only [vbyte, ofVWords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, ht, decide_true,
    Bool.true_and]
  rcases (by omega : k < 4 ∨ (4 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 12) ∨ 12 ≤ k) with h | h | h | h <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right] <;>
    exact congrArg _ (by omega)

theorem ext32 {a b : BitVec 32} (h : ∀ q < 4, a.extractLsb' (8 * q) 8 = b.extractLsb' (8 * q) 8) :
    a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  have := congrArg (BitVec.getLsbD · (t % 8)) (h (t / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true (Nat.mod_lt t (by omega : 8 > 0)),
    Bool.true_and] at this
  rwa [show 8 * (t / 8) + t % 8 = t by omega] at this

theorem vword0_byte (x : BitVec 128) {q : Nat} (hq : q < 4) :
    (vword x 0).extractLsb' (8 * q) 8 = vbyte x q := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp only [vword, vbyte, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and,
    show 8 * q + t < 32 by omega, Nat.mul_zero, Nat.zero_add]

theorem sub32_byte (w : BitVec 32) {q : Nat} (hq : q < 4) :
    (sub32 w).extractLsb' (8 * q) 8 = aesSbox (w.extractLsb' (8 * q) 8) := by
  obtain ⟨e0, e1, e2, e3⟩ := extract_cat (aesSbox (w.extractLsb' 24 8)) (aesSbox (w.extractLsb' 16 8))
    (aesSbox (w.extractLsb' 8 8)) (aesSbox (w.extractLsb' 0 8))
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
  · exact e0
  · exact e1
  · exact e2
  · exact e3

theorem xor_zero128 (x : BitVec 128) : x ^^^ 0 = x := BitVec.xor_zero

/-- `aese` of a word in every column, with a zero round key, is `SubWord`. -/
theorem aese_dup (w : BitVec 32) :
    vword (aesMapBytes aesSbox (aesShiftRows (ofVWords w w w w ^^^ 0))) 0 = sub32 w := by
  apply ext32; intro q hq
  rw [vword0_byte _ hq, vbyte_mapBytes _ _ (by omega), vbyte_shiftRows _ (by omega), xor_zero128,
    vbyte_dup _ (by omega), sub32_byte _ hq]
  congr 3
  omega

end VG.Proof.Aes.AArch64.Aese

/-!
## The words' code
-/

namespace VG.Proof.Aes.AArch64.Aese.Key

open VG VG.AArch64
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese (rc wregs wreg subW word expandN expandKey)

section
variable (s₀ : State)

abbrev kp : Addr := s₀.gpr .x0
abbrev klen : Nat := (s₀.gpr .x1).toNat
abbrev schp : Addr := s₀.gpr .x2
abbrev schR : Region := ⟨schp s₀, 240⟩
abbrev keyR : Region := ⟨kp s₀, klen s₀⟩
/-- The words of the schedule. -/
abbrev Ws (nk : Nat) : Nat → BitVec 32 := W s₀.mem (kp s₀) nk

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀]
  wr : s₀.wr = [schR s₀, ⟨s₀.gpr .x3, 512⟩]
  k_s : (keyR s₀).Disjoint (schR s₀)
  lens : klen s₀ = 16 ∨ klen s₀ = 24 ∨ klen s₀ = 32

theorem pre_of {s₀ : State} (h : Proof.Aes.expandKeyAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, _, _, h6⟩ := h
  exact ⟨h1, h2, h3, h6⟩

/-- Words `0 … i − 1` are stored, and words `i − Nk … i − 1` are in their registers. -/
structure KInv (s₀ : State) (nk i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = kp s₀
  x2 : s.gpr .x2 = schp s₀
  v0 : s.v .v0 = 0
  win : ∀ j < i, i ≤ j + nk → (s.gpr (wreg nk j)).setWidth 32 = Ws s₀ nk j
  frame : Frame [schR s₀] s₀.mem s.mem
  good : Good s.mem (schp s₀) (Ws s₀ nk) i
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-! ## Registers -/

theorem wregs_inj : ∀ a < 8, ∀ b < 8, wregs.getD a .x4 = wregs.getD b .x4 → a = b := by decide

theorem wregs_ne : ∀ a < 8, wregs.getD a .x4 ≠ .x0 ∧ wregs.getD a .x4 ≠ .x2 ∧
    wregs.getD a .x4 ≠ .x9 ∧ wregs.getD a .x4 ≠ .x10 := by decide

theorem wreg_ne {nk : Nat} (h8 : nk ≤ 8) (h0 : 0 < nk) (j : Nat) :
    wreg nk j ≠ .x0 ∧ wreg nk j ≠ .x2 ∧ wreg nk j ≠ .x9 ∧ wreg nk j ≠ .x10 :=
  wregs_ne _ (by have := Nat.mod_lt j h0; omega)

/-- Words less than `Nk` apart are in different registers. -/
theorem wreg_inj {nk : Nat} (h8 : nk ≤ 8) {j i : Nat} (h1 : j < i) (h2 : i < j + nk) :
    wreg nk j ≠ wreg nk i := by
  intro h
  have e := wregs_inj _ (by have := Nat.mod_lt j (show 0 < nk by omega); omega) _
    (by have := Nat.mod_lt i (show 0 < nk by omega); omega) h
  have h0 := Nat.sub_mod_eq_zero_of_mod_eq e.symm
  rw [Nat.mod_eq_of_lt (show i - j < nk by omega)] at h0
  omega

theorem wreg_mod {nk i : Nat} (h : nk ≤ i) : wreg nk i = wreg nk (i - nk) := by
  simp only [wreg]
  rw [Nat.mod_eq_sub_mod h]

/-! ## Instructions -/

theorem wp_cons {i : Instr} {is : List Instr} {s : State} {Q : State → Prop} (P : State → Prop)
    (h₁ : WP isa (.block [i]) s P) (h₂ : ∀ s', P s' → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q := by
  rw [show (i :: is) = [i] ++ is from rfl, WP.block_append_iff]; exact WP.mono h₁ h₂

theorem Fr.write {gs : List Reg} {vs : List VReg} {s : State} {sz : Size} {r : Reg} (hr : r ∈ gs)
    (v : BitVec sz.bits) : Fr gs vs s (s.write sz r v) :=
  ⟨fun r' h => by simp [State.write, show r' ≠ r from fun e => h (e ▸ hr)], fun _ _ => rfl, rfl, rfl,
    rfl, rfl⟩

theorem Fr.setV {gs : List Reg} {vs : List VReg} {s : State} {r : VReg} (hr : r ∈ vs)
    (v : BitVec 128) : Fr gs vs s (s.setV r v) :=
  ⟨fun _ _ => rfl, fun r' h => by simp [State.setV, show r' ≠ r from fun e => h (e ▸ hr)], rfl, rfl,
    rfl, rfl⟩

theorem write32 (s : State) (r : Reg) (v : BitVec 32) : ((s.write .w r v).gpr r).setWidth 32 = v := by
  simp [State.write]

theorem eor_ok (d n m : Reg) (s : State) :
    WP isa (.block [.logic .eor .w d n m]) s fun s' =>
      (s'.gpr d).setWidth 32 = (s.gpr n).setWidth 32 ^^^ (s.gpr m).setWidth 32 ∧ Fr [d] [] s s' :=
  WP.of_runBlock ⟨s.write .w d (s.read .w n ^^^ s.read .w m), rfl, write32 _ _ _,
    Fr.write (by simp) _⟩

theorem ror_ok (s : State) :
    WP isa (.block [.ror .w .x9 .x9 8]) s fun s' =>
      (s'.gpr .x9).setWidth 32 = ((s.gpr .x9).setWidth 32).rotateRight 8 ∧ Fr [.x9] [] s s' :=
  WP.of_runBlock ⟨s.write .w .x9 ((s.read .w .x9).rotateRight 8), rfl, write32 _ _ _,
    Fr.write (by simp) _⟩

theorem movz_ok (d : Reg) (imm : BitVec 16) (s : State) :
    WP isa (.block [.movz .w d imm 0]) s fun s' =>
      (s'.gpr d).setWidth 32 = imm.setWidth 32 ∧ Fr [d] [] s s' :=
  WP.of_runBlock ⟨s.write .w d (imm.setWidth 32), by
    rw [runBlock_cons, exec_movz_w, runStep_some, runBlock_nil], write32 _ _ _, Fr.write (by simp) _⟩

theorem subW_ok (p : Reg) (s : State) (hv0 : s.v .v0 = 0) :
    WP isa (.block (subW p)) s fun s' =>
      (s'.gpr .x9).setWidth 32 = sub32 ((s.gpr p).setWidth 32) ∧ Fr [.x9] [.v1] s s' := by
  let w := (s.gpr p).setWidth 32
  let s₁ := s.setV .v1 (ofVWords w w w w)
  let s₂ := s₁.setV .v1 (aesMapBytes aesSbox (aesShiftRows (s₁.v .v1 ^^^ s₁.v .v0)))
  refine WP.of_runBlock ⟨s₂.write .w .x9 (vword (s₂.v .v1) 0), rfl, ?_, ?_⟩
  · rw [write32]
    simp only [s₂, s₁, setV_v_self]
    rw [setV_v_of_ne _ _ (by decide), hv0]
    exact aese_dup _
  · exact ((Fr.setV (by simp) _).trans (Fr.setV (by simp) _)).trans (Fr.write (by simp) _)

/-! ## A word -/

theorem Pre.len_lt {s₀ : State} (_ : Pre s₀) : klen s₀ < 2 ^ 64 := (s₀.gpr .x1).isLt

/-- Storing word `i`, computed into its register. -/
theorem store_ok {s₀ : State} (hp : Pre s₀) {nk i : Nat} (h8 : nk ≤ 8) (h0 : 0 < nk)
    (hi : 4 * i + 4 ≤ 240) {s s₁ : State} (hI : KInv s₀ nk i s)
    (hf : Fr [wreg nk i, .x9, .x10] [.v1] s s₁) (hv : (s₁.gpr (wreg nk i)).setWidth 32 = Ws s₀ nk i) :
    WP isa (.block [.str .w (wreg nk i) .x2 (4 * i)]) s₁ (KInv s₀ nk (i + 1)) := by
  obtain ⟨n0, n2, n9, n10⟩ := wreg_ne h8 h0 i
  have g0 : s₁.gpr .x0 = kp s₀ := by rw [hf.gpr _ (by simp [Ne.symm n0]), hI.x0]
  have g2 : s₁.gpr .x2 = schp s₀ := by rw [hf.gpr _ (by simp [Ne.symm n2]), hI.x2]
  have hw : InRegions s₁.wr (s₁.gpr .x2 + BitVec.ofNat 64 (4 * i)) 4 :=
    ⟨schR s₀, by rw [hf.wr, hI.wr, hp.wr]; simp, by rw [g2]; exact Offset.contains_base _ hi (by omega)⟩
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_str_w (by omega) hw, runStep_some,
    runBlock_nil], ?_⟩
  rw [g2]
  refine ⟨g0, g2, by rw [show _ = s₁.v .v0 from rfl, hf.v _ (by simp)]; exact hI.v0,
    fun j hj1 hj2 => ?_, ?_, ?_, hf.rd.trans hI.rd, hf.wr.trans hI.wr⟩
  · show (s₁.gpr (wreg nk j)).setWidth 32 = _
    by_cases hj : j = i
    · subst hj; exact hv
    · obtain ⟨m0, m2, m9, m10⟩ := wreg_ne h8 h0 j
      rw [hf.gpr _ (by simp [wreg_inj h8 (show j < i by omega) (by omega), m9, m10])]
      exact hI.win j (by omega) (by omega)
  · show Frame _ _ (s₁.mem.writeW _ _)
    rw [hf.mem]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ hi (by omega))
  · show Good (s₁.mem.writeW _ _) _ _ _
    rw [hf.mem]
    exact good_store hI.good hv hi

theorem key_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [schR s₀] s₀.mem m) {i : Nat}
    (hi : 4 * i + 4 ≤ klen s₀) :
    m.readW (kp s₀ + BitVec.ofNat 64 (4 * i)) 32 = s₀.mem.readW (kp s₀ + BitVec.ofNat 64 (4 * i)) 32 :=
  hf.readW (r := keyR s₀) (Offset.contains_base _ hi (by have := hp.len_lt; omega))
    (by simp only [List.mem_singleton, forall_eq]; exact hp.k_s) (by decide)

theorem word_ok {s₀ : State} (hp : Pre s₀) {nk : Nat} (hnk : nk = 4 ∨ nk = 6 ∨ nk = 8)
    (hl : klen s₀ = 4 * nk) {i : Nat} (hi : i < 4 * (nk + 7)) {s : State} (hI : KInv s₀ nk i s) :
    WP isa (.block (word nk i)) s (KInv s₀ nk (i + 1)) := by
  have h8 : nk ≤ 8 := by omega
  have h0 : 0 < nk := by omega
  have h240 : 4 * i + 4 ≤ 240 := by omega
  have st := fun {s₁} hf hv => store_ok hp h8 h0 h240 (s₁ := s₁) hI hf hv
  obtain ⟨n0, n2, n9, n10⟩ := wreg_ne h8 h0 i
  simp only [word]
  by_cases hk : i < nk
  · -- A word of the key.
    rw [ite_eq_left hk, WP.block_append_iff]
    have hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * i)) 4 :=
      ⟨keyR s₀, by rw [hI.rd, hp.rd]; simp, by
        rw [hI.x0]; exact Offset.contains_base _ (by omega) (by have := hp.len_lt; omega)⟩
    refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_ldr_w (by omega) hin, runStep_some,
      runBlock_nil], st (Fr.write (by simp) _) ?_⟩
    rw [write32, hI.x0, key_frame hp hI.frame (by omega)]
    exact (W_lt hk).symm
  -- The other words: `w[i − Nk] ⊕ temp`, where `w[i − Nk]` is.
  rw [ite_eq_right hk]
  have hr : wreg nk i = wreg nk (i - nk) := wreg_mod (by omega)
  have hA : (s.gpr (wreg nk i)).setWidth 32 = Ws s₀ nk (i - nk) := by
    rw [hr]; exact hI.win _ (by omega) (by omega)
  have hP : (s.gpr (wreg nk (i - 1))).setWidth 32 = Ws s₀ nk (i - 1) := hI.win _ (by omega) (by omega)
  have hW : Ws s₀ nk i = Ws s₀ nk (i - nk) ^^^ temp32 nk i (Ws s₀ nk (i - 1)) := W_ge h0 (by omega)
  by_cases h1 : i % nk = 0
  · rw [ite_eq_left h1, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (subW_ok _ s hI.v0) fun s₁ ⟨e₁, f₁⟩ => ?_
    refine wp_cons _ (ror_ok s₁) fun s₂ ⟨e₂, f₂⟩ => ?_
    refine wp_cons _ (movz_ok .x10 _ s₂) fun s₃ ⟨e₃, f₃⟩ => ?_
    refine wp_cons _ (eor_ok .x9 .x9 .x10 s₃) fun s₄ ⟨e₄, f₄⟩ => ?_
    refine WP.mono (eor_ok _ _ .x9 s₄) fun s₅ ⟨e₅, f₅⟩ => ?_
    have f : Fr [wreg nk i, .x9, .x10] [.v1] s s₅ :=
      (((f₁.mono (by simp) (by simp)).trans (f₂.mono (by simp) (by simp))).trans
        ((f₃.mono (by simp) (by simp)).trans (f₄.mono (by simp) (by simp)))).trans
        (f₅.mono (by simp) (by simp))
    refine st f ?_
    rw [e₅, e₄, e₃, f₃.gpr .x9 (by simp), e₂, e₁, f₄.gpr _ (by simp [n9]), f₃.gpr _ (by simp [n10]),
      f₂.gpr _ (by simp [n9]), f₁.gpr _ (by simp [n9]), hA, hW, temp32, ite_eq_left h1, hP,
      BitVec.setWidth_setWidth (by omega)]
  by_cases h2 : nk > 6 ∧ i % nk = 4
  · rw [ite_eq_right h1, ite_eq_left h2, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (subW_ok _ s hI.v0) fun s₁ ⟨e₁, f₁⟩ => ?_
    refine WP.mono (eor_ok _ _ .x9 s₁) fun s₂ ⟨e₂, f₂⟩ => ?_
    refine st ((f₁.mono (by simp) (by simp)).trans (f₂.mono (by simp) (by simp))) ?_
    rw [e₂, e₁, f₁.gpr _ (by simp [n9]), hA, hW, temp32, ite_eq_right h1, ite_eq_left h2, hP]
  · rw [ite_eq_right h1, ite_eq_right h2, WP.block_append_iff]
    refine WP.mono (eor_ok _ _ _ s) fun s₁ ⟨e₁, f₁⟩ => ?_
    refine st (f₁.mono (by simp) (by simp)) ?_
    rw [e₁, hA, hP, hW, temp32, ite_eq_right h1, ite_eq_right h2]

/-! ## The whole function -/

theorem expandN_ok {s₀ : State} (hp : Pre s₀) {nk : Nat} (hnk : nk = 4 ∨ nk = 6 ∨ nk = 8)
    (hl : klen s₀ = 4 * nk) {s : State} (hI : KInv s₀ nk 0 s) :
    WP isa (.block (expandN nk)) s (KInv s₀ nk (4 * (nk + 7))) := by
  unfold expandN
  exact wp_range_flatMap (M := isa) (f := word nk) (KInv s₀ nk) (fun _ _ hk h => word_ok hp hnk hl hk h)
    _ (Nat.le_refl _) s hI

theorem fin {s₀ : State} {nk : Nat} (h0 : 0 < nk) (hl : klen s₀ = 4 * nk) {s : State}
    (hI : KInv s₀ nk (4 * (nk + 7)) s) : Proof.Aes.expandKeyAArch64.post s₀ s := by
  have hl' : (s₀.gpr .x1).toNat = 4 * nk := hl
  show Spec.Aes.bytesAt s.mem (schp s₀) (16 * (Spec.Aes.rounds ((s₀.gpr .x1).toNat / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem (kp s₀) (s₀.gpr .x1).toNat)
  rw [hl', show 4 * nk / 4 = nk by omega, expandKey_eq s₀.mem _ h0, Spec.Aes.rounds,
    show 16 * (nk + 6 + 1) = 4 * (4 * (nk + 6 + 1)) by omega]
  exact bytesAt_eq s.mem _ _ _ fun i hi => hI.good i (by omega)

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa expandKey s₀ (Proof.Aes.expandKeyAArch64.post s₀) := by
  have hx1 : s₀.gpr .x1 = BitVec.ofNat 64 (klen s₀) := by simp [klen]
  have hlt := hp.len_lt
  refine WP.seq ?_
  rw [WP.block_cons_iff]; refine ⟨s₀.setV .v0 0, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 24) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 32) (by decide), WP.block_nil ?_⟩
  let s₁ := ((s₀.setV .v0 0).write .x .x9 ((s₀.setV .v0 0).read .x .x1 - BitVec.ofNat _ 24)).write .x
    .x10 (((s₀.setV .v0 0).write .x .x9 ((s₀.setV .v0 0).read .x .x1 - BitVec.ofNat _ 24)).read .x .x1 -
      BitVec.ofNat _ 32)
  show WP isa _ s₁ _
  have hI : ∀ nk, KInv s₀ nk 0 s₁ := fun nk =>
    ⟨rfl, rfl, by simp [s₁, State.write, State.setV], fun _ h => absurd h (Nat.not_lt_zero _),
      Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl⟩
  have e9 : AArch64.eval (.zero .x .x9) s₁ = some (decide (klen s₀ = 24)) := by
    simp only [AArch64.eval, s₁, State.read, State.write, State.setV, reduceCtorEq, ite_false,
      ite_true, BitVec.setWidth_eq, hx1]
    rw [Offset.ofNat_sub_ofNat_beq hlt (by decide)]
  have e10 : AArch64.eval (.zero .x .x10) s₁ = some (decide (klen s₀ = 32)) := by
    simp only [AArch64.eval, s₁, State.read, State.write, State.setV, reduceCtorEq, ite_false,
      ite_true, BitVec.setWidth_eq, hx1]
    rw [Offset.ofNat_sub_ofNat_beq hlt (by decide)]
  refine WP.ite _ e9 (fun h => ?_) (fun h => ?_)
  · have h24 : klen s₀ = 24 := by simpa using h
    exact WP.mono (expandN_ok hp (nk := 6) (by decide) h24 (hI 6)) fun _ h => fin (by decide) h24 h
  refine WP.ite _ e10 (fun h' => ?_) (fun h' => ?_)
  · have h32 : klen s₀ = 32 := by simpa using h'
    exact WP.mono (expandN_ok hp (nk := 8) (by decide) h32 (hI 8)) fun _ h => fin (by decide) h32 h
  · have h16 : klen s₀ = 16 := by
      simp only [decide_eq_false_iff_not] at h h'; rcases hp.lens with e | e | e <;> omega
    exact WP.mono (expandN_ok hp (nk := 4) (by decide) h16 (hI 4)) fun _ h => fin (by decide) h16 h

theorem expandKey_correct (s : State) (hs : Proof.Aes.expandKeyAArch64.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyAArch64.post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ :=
    WP.gprs (rs := preserved) (correct (pre_of hs)) (by decide +kernel) (by decide +kernel)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩

theorem expandKey_ct : ConstantTime isa Proof.Aes.expandKeyAArch64.pre
    Proof.Aes.expandKeyAArch64.pub expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem expandKey_verified :
    Verified AArch64.target expandKey (Spec.Aes.expandKeyContract AArch64.abi) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Proof.Aes.expandKeyAArch64,
      AArch64.abi, AArch64.argRegs] [Proof.Aes.AArch64.ekSatState] using
      Proof.Aes.AArch64.ekSatState)

end VG.Proof.Aes.AArch64.Aese.Key
