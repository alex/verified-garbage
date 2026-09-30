import VerifiedGarbage.Proof.Gcm.X86.Step
import VerifiedGarbage.Proof.Gcm.X86.GhashCT
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# GHASH on x86 (32-bit): the whole function

Untrusted: everything here is checked by Lean.

Each block loads `Y ⊕ X` (big-endian words, `bswap`) into the scratch
buffer, `Z := 0` and `V := H`, runs the 128 steps (`Step.lean`), and
stores `Z` as the new `Y`. The prologue saves the callee-saved registers
in the scratch buffer with the data pointer and the count, and the
epilogue restores them. Constant time is `GhashCT.lean`.
-/

namespace VG.Proof.Gcm.X86

open VG VG.X86 VG.Impl.Gcm.X86 VG.Proof.Gcm VG.Proof.Aes.X86
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_add wp_addi wp_subi wp_ldm wp_xorm wp_stm wp_xor wp_test
  wp_bswap ofNat_pred ofNat_beq_zero)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## Blocks as big-endian words -/

theorem bswap_word_bit (m : Mem) {P : BitVec 32} (hP : P.toNat + 16 ≤ 2 ^ 32) {v k j : Nat} (hv : v < 4)
    (hk : k < 4) (hj : j < 8) :
    (bswap (m.readW (addr P (4 * v)) 32)).getLsbD (8 * k + j) =
      (blockAt m (P.setWidth 64)).getLsbD (32 * (3 - v) + (8 * k + j)) := by
  rw [bswap_bit _ hk hj, readW_bit _ _ (by omega) hj, addr_add64 (by omega), addr_eq (by omega),
    show 32 * (3 - v) + (8 * k + j) = 8 * (15 - (4 * v + (3 - k))) + j by omega,
    Proof.Aes.blockAt_bit _ _ (by omega) hj]

/-- A block is its four big-endian words. -/
theorem blockAt_words (m : Mem) {P : BitVec 32} (hP : P.toNat + 16 ≤ 2 ^ 32) :
    blockAt m (P.setWidth 64) = cat4 (bswap (m.readW (addr P 0) 32)) (bswap (m.readW (addr P 4) 32))
      (bswap (m.readW (addr P 8) 32)) (bswap (m.readW (addr P 12) 32)) := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [getLsbD_cat4]
  have e : ∀ v < 4, 32 * (3 - v) ≤ t → t < 32 * (3 - v) + 32 →
      (blockAt m (P.setWidth 64)).getLsbD t =
        (bswap (m.readW (addr P (4 * v)) 32)).getLsbD (t - 32 * (3 - v)) := fun v hv h1 h2 => by
    rw [show t - 32 * (3 - v) = 8 * ((t - 32 * (3 - v)) / 8) + (t - 32 * (3 - v)) % 8 by omega,
      bswap_word_bit m hP hv (by omega) (by omega)]
    congr 1; omega
  split
  · exact e 3 (by decide) (by omega) (by omega)
  · split
    · exact e 2 (by decide) (by omega) (by omega)
    · split
      · exact e 1 (by decide) (by omega) (by omega)
      · exact e 0 (by decide) (by omega) (by omega)

theorem bswap_bswap (v : BitVec 32) : bswap (bswap v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [show t = 8 * (t / 8) + t % 8 by omega, bswap_bit _ (by omega) (by omega),
    bswap_bit _ (by omega) (by omega)]
  congr 1; omega

theorem xw_cat4 (a b c d : BitVec 32) :
    xw (cat4 a b c d) 0 = a ∧ xw (cat4 a b c d) 1 = b ∧ xw (cat4 a b c d) 2 = c ∧ xw (cat4 a b c d) 3 = d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply BitVec.eq_of_getLsbD_eq; intro t ht) <;>
    simp only [xw, BitVec.getLsbD_extractLsb', getLsbD_cat4, ht, decide_true, Bool.true_and] <;>
    split_ifs <;> first | omega | (congr 1; omega)

theorem xw_cat4_0 (a b c d : BitVec 32) : xw (cat4 a b c d) 0 = a := (xw_cat4 a b c d).1
theorem xw_cat4_1 (a b c d : BitVec 32) : xw (cat4 a b c d) 1 = b := (xw_cat4 a b c d).2.1
theorem xw_cat4_2 (a b c d : BitVec 32) : xw (cat4 a b c d) 2 = c := (xw_cat4 a b c d).2.2.1
theorem xw_cat4_3 (a b c d : BitVec 32) : xw (cat4 a b c d) 3 = d := (xw_cat4 a b c d).2.2.2

theorem xw_xor (x y : Block) (w : Nat) : xw (x ^^^ y) w = xw x w ^^^ xw y w := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp only [xw, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor]
  cases decide (t < 32) <;> simp

/-! ## Loading a block -/

/-- `V`'s word `k`, from `H`. -/
def vLoad (k : Nat) : List Instr := [.mov (vReg k) (.mem (at_ .ebp (4 * k))), .bswap (vReg k)]

/-- The start of `load`: `Y ⊕ X`, `Z := 0`, and `ebp := h`. -/
def loadHead : List Instr :=
  ((((([.mov .esi (.mem (at_ .edi 48)), .mov .ebp (.mem (at_ .esp 8))] : List Instr) ++ loadX 0) ++ loadX 1) ++
    loadX 2) ++ loadX 3) ++
  ([.mov .eax (.imm 0), .store (at_ .edi 16) .eax, .store (at_ .edi 20) .eax, .store (at_ .edi 24) .eax,
    .store (at_ .edi 28) .eax, .mov .ebp (.mem (at_ .esp 4))] : List Instr)

theorem load_eq : load = ((((loadHead ++ vLoad 0) ++ vLoad 1) ++ vLoad 2) ++ vLoad 3) ++
    ([.mov .esi (.imm 4), .store (at_ .edi 56) .esi] : List Instr) := rfl

/-- Word `w` of `Y ⊕ X`. -/
def vX (m : Mem) (Yp Xp : BitVec 32) (w : Nat) : BitVec 32 :=
  bswap (m.readW (addr Yp (4 * w)) 32) ^^^ bswap (m.readW (addr Xp (4 * w)) 32)

/-- The memory after `loadHead`. -/
def headMem (m : Mem) (B Yp Xp : BitVec 32) : Mem :=
  (((((((m.writeW (addr B (4 * 0)) (vX m Yp Xp 0)).writeW (addr B (4 * 1)) (vX m Yp Xp 1)).writeW
    (addr B (4 * 2)) (vX m Yp Xp 2)).writeW (addr B (4 * 3)) (vX m Yp Xp 3)).writeW (addr B 16) (0 : BitVec 32)).writeW
    (addr B 20) (0 : BitVec 32)).writeW (addr B 24) (0 : BitVec 32)).writeW (addr B 28) (0 : BitVec 32)

section
variable {s : State} {P : State → Prop}

/-- Word `w` of `Y ⊕ X`. -/
theorem loadX_wp (w : Nat) {B Yp Xp : BitVec 32} (hb : s.gpr .edi = B) (hy : s.gpr .ebp = Yp)
    (hx : s.gpr .esi = Xp) (iy : InRegions (s.rd ++ s.wr) (addr Yp (4 * w)) 4)
    (ix : InRegions (s.rd ++ s.wr) (addr Xp (4 * w)) 4) (ib : InRegions s.wr (addr B (4 * w)) 4)
    (h : ∀ s', s'.mem = s.mem.writeW (addr B (4 * w))
        (bswap (s.mem.readW (addr Yp (4 * w)) 32) ^^^ bswap (s.mem.readW (addr Xp (4 * w)) 32)) →
      (∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (loadX w)) s P := by
  refine wp_ldm hy iy fun s₁ u₁ => wp_bswap fun s₂ u₂ => ?_
  refine wp_ldm (B := Xp) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hx)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact ix) fun s₃ u₃ => wp_bswap fun s₄ u₄ => ?_
  refine wp_xor fun s₅ u₅ => wp_stm (B := B) (by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide)]; exact hb)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact ib) fun s₆ u₆ => WP.block_nil ?_
  refine h s₆ ?_ (fun r h1 h2 => ?_) (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₆.mem, u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr,
      u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.gpr, u₅.other r h1, u₄.other r h2, u₃.other r h2, u₂.other r h1, u₁.other r h1]

/-- `V`'s word `k`. -/
theorem vLoad_wp (k : Nat) {Hp : BitVec 32} (hp : s.gpr .ebp = Hp)
    (ih : InRegions (s.rd ++ s.wr) (addr Hp (4 * k)) 4)
    (h : ∀ s', s'.gpr (vReg k) = bswap (s.mem.readW (addr Hp (4 * k)) 32) →
      (∀ r, r ≠ vReg k → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (vLoad k)) s P := by
  refine wp_ldm hp ih fun s₁ u₁ => wp_bswap fun s₂ u₂ => WP.block_nil ?_
  exact h s₂ (by rw [u₂.gpr, u₁.gpr]) (fun r hr => by rw [u₂.other r hr, u₁.other r hr])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])

end

/-! ## Storing `Y` -/

/-- Word `k` of `Z`, big-endian, to `Y`. -/
def zStore (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (zOff k))), .bswap .eax, .store (at_ .esi (4 * k)) .eax]

/-- The memory after the new `Y` is stored. -/
def yMem (m : Mem) (B Yp : BitVec 32) : Mem :=
  (((m.writeW (addr Yp (4 * 0)) (bswap (zw m B 0))).writeW (addr Yp (4 * 1)) (bswap (zw m B 1))).writeW
    (addr Yp (4 * 2)) (bswap (zw m B 2))).writeW (addr Yp (4 * 3)) (bswap (zw m B 3))

theorem store_eq : store = (((([.mov .esi (.mem (at_ .esp 8))] : List Instr) ++ zStore 0) ++ zStore 1) ++
    zStore 2) ++ zStore 3 ++ ([.mov .esi (.mem (at_ .edi 48)), .alu .add .esi (.imm 16),
      .store (at_ .edi 48) .esi, .mov .esi (.mem (at_ .edi 52)), .alu .sub .esi (.imm 1),
      .store (at_ .edi 52) .esi] : List Instr) := rfl

/-! ## The loop over the blocks -/

/-- The setting of the loop over the blocks, from the state `s₁` after the
prologue: `H` at `Hp`, `Y` at `Yp`, the `n` blocks at `Dp`, the scratch
buffer at `B`, and the arguments above `E`. -/
structure BSetup (s₁ : State) (Hp Yp Dp B E : BitVec 32) (n : Nat) : Prop where
  hR : reg32 Hp 16 ∈ s₁.rd
  dR : reg32 Dp (16 * n) ∈ s₁.rd
  yW : reg32 Yp 16 ∈ s₁.wr
  sW : reg32 B 256 ∈ s₁.wr
  fH : Hp.toNat + 16 ≤ 2 ^ 32
  fY : Yp.toNat + 16 ≤ 2 ^ 32
  fD : Dp.toNat + 16 * n ≤ 2 ^ 32
  fB : B.toNat + 256 ≤ 2 ^ 32
  dHY : (reg32 Hp 16).Disjoint (reg32 Yp 16)
  dHS : (reg32 Hp 16).Disjoint (reg32 B 256)
  dYD : (reg32 Yp 16).Disjoint (reg32 Dp (16 * n))
  dYS : (reg32 Yp 16).Disjoint (reg32 B 256)
  dDS : (reg32 Dp (16 * n)).Disjoint (reg32 B 256)
  fE : E.toNat + 24 ≤ 2 ^ 32
  argIn : ∀ i < 2, InRegions s₁.rd (addr E (4 + 4 * i)) 4
  argH : s₁.mem.readW (addr E 4) 32 = Hp
  argY : s₁.mem.readW (addr E 8) 32 = Yp
  aY : (⟨addr E 4, 8⟩ : Region).Disjoint (reg32 Yp 16)
  aS : (⟨addr E 4, 8⟩ : Region).Disjoint (reg32 B 256)

/-- What the loop writes. -/
abbrev bRegions (Yp B : BitVec 32) : List Region := [reg32 Yp 16, reg32 B 32, ⟨addr B dOff, 16⟩]

/-- Before block `b`. -/
structure BInv (s₁ : State) (Hp Yp Dp B E : BitVec 32) (n b : Nat) (s : State) : Prop where
  hb : b ≤ n
  edi : s.gpr .edi = B
  esp : s.gpr .esp = E
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  dslot : s.mem.readW (addr B dOff) 32 = Dp + BitVec.ofNat 32 (16 * b)
  nslot : s.mem.readW (addr B nOff) 32 = BitVec.ofNat 32 (n - b)
  y : blockAt s.mem (Yp.setWidth 64) = ghashFrom (blockAt s₁.mem (Hp.setWidth 64))
    (blockAt s₁.mem (Yp.setWidth 64)) (blocksAt s₁.mem (Dp.setWidth 64) b)
  frame : Frame (bRegions Yp B) s₁.mem s.mem

section
variable {s₁ : State} {Hp Yp Dp B E : BitVec 32} {n : Nat} (hs : BSetup s₁ Hp Yp Dp B E n)
include hs

theorem BSetup.rY (m : Mem) (v : BitVec 32) {o e : Nat} (ho : o + 4 ≤ 256) (he : e + 4 ≤ 16) :
    (m.writeW (addr B o) v).readW (addr Yp e) 32 = m.readW (addr Yp e) 32 :=
  rd_wr_other hs.dYS (reg_contains hs.fY he (by decide)) (reg_contains hs.fB ho (by decide))

theorem BSetup.rH (m : Mem) (v : BitVec 32) {o e : Nat} (ho : o + 4 ≤ 256) (he : e + 4 ≤ 16) :
    (m.writeW (addr B o) v).readW (addr Hp e) 32 = m.readW (addr Hp e) 32 :=
  rd_wr_other hs.dHS (reg_contains hs.fH he (by decide)) (reg_contains hs.fB ho (by decide))

theorem BSetup.rD (m : Mem) (v : BitVec 32) {o e : Nat} (ho : o + 4 ≤ 256) (he : e + 4 ≤ 16 * n) :
    (m.writeW (addr B o) v).readW (addr Dp e) 32 = m.readW (addr Dp e) 32 :=
  rd_wr_other hs.dDS (reg_contains hs.fD he (by decide)) (reg_contains hs.fB ho (by decide))

theorem BSetup.rB (m : Mem) (v : BitVec 32) {o e : Nat} (ho : o + 4 ≤ 256) (he : e + 4 ≤ 16) :
    (m.writeW (addr Yp e) v).readW (addr B o) 32 = m.readW (addr B o) 32 :=
  rd_wr_other hs.dYS.symm (reg_contains hs.fB ho (by decide)) (reg_contains hs.fY he (by decide))

theorem BSetup.fX {b : Nat} (hb : b < n) : (Dp + BitVec.ofNat 32 (16 * b)).toNat + 16 ≤ 2 ^ 32 := by
  have fD := hs.fD
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * b) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem BSetup.argC {o : Nat} (h1 : 4 ≤ o) (h2 : o + 4 ≤ 12) :
    (⟨addr E 4, 8⟩ : Region).Contains (addr E o) (32 / 8) :=
  part_contains (N := 12) (by have := hs.fE; omega) (by decide) h1 (by omega) (by decide)

theorem BSetup.dA : ∀ r ∈ bRegions Yp B, Region.Disjoint ⟨addr E 4, 8⟩ r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.aY
  · exact hs.aS.sub_right (Region.sub_prefix (by decide))
  · exact hs.aS.sub_right (part_sub_reg hs.fB (by simp only [dOff]; omega))

theorem BSetup.dM {R : Region} (hR : R.Disjoint (reg32 B 256)) : ∀ r ∈ mRegions B, R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hR.sub_right (Region.sub_prefix (by decide))
  · exact hR.sub_right (part_sub_reg hs.fB (by simp only [wcOff]; omega))

theorem BSetup.headMem_frame (m : Mem) (Xp : BitVec 32) : Frame (mRegions B) m (headMem m B Yp Xp) := by
  have h32 : reg32 B 32 ∈ mRegions B := List.mem_cons_self ..
  have c : ∀ o, o + 4 ≤ 32 → (reg32 B 32).Contains (addr B o) (32 / 8) := fun o ho =>
    reg_contains (by have := hs.fB; omega) ho (by decide)
  exact (((((((Frame.refl _ _).writeW h32 _ (c _ (by decide))).writeW h32 _ (c _ (by decide))).writeW h32 _
    (c _ (by decide))).writeW h32 _ (c _ (by decide))).writeW h32 _ (c _ (by decide))).writeW h32 _
    (c _ (by decide))).writeW h32 _ (c _ (by decide)) |>.writeW h32 _ (c _ (by decide))

/-- `Y ⊕ X` of block `b`, `Z := 0`, and `ebp := h`. -/
theorem head_ok {b : Nat} {s : State} (hi : BInv s₁ Hp Yp Dp B E n b s) (hb : b < n) :
    WP isa (.block loadHead) s fun t =>
      t.mem = headMem s.mem B Yp (Dp + BitVec.ofNat 32 (16 * b)) ∧ t.gpr .edi = B ∧ t.gpr .ebp = Hp ∧
        t.gpr .esp = E ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fB := hs.fB; have fY := hs.fY; have fD := hs.fD
  have hbn : 16 * b + 16 ≤ 16 * n := by omega
  let Xp := Dp + BitVec.ofNat 32 (16 * b)
  have inB : ∀ (t : State), t.wr = s.wr → ∀ o, o + 4 ≤ 256 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht, hi.wr]; exact in_reg hs.sW fB ho (by decide)
  have inY : ∀ (t : State), t.rd = s.rd → t.wr = s.wr → ∀ e, e + 4 ≤ 16 →
      InRegions (t.rd ++ t.wr) (addr Yp e) 4 :=
    fun t h1 h2 e he => by rw [h1, h2, hi.wr]; exact in_rd (in_reg hs.yW fY he (by decide))
  have inX : ∀ (t : State), t.rd = s.rd → t.wr = s.wr → ∀ e, e + 4 ≤ 16 →
      InRegions (t.rd ++ t.wr) (addr Xp e) 4 :=
    fun t h1 h2 e he => by
      rw [h1, h2, hi.rd, addr_add]; exact in_rd_left (in_reg hs.dR fD (by omega) (by decide))
  have inA : ∀ (t : State), t.rd = s.rd → ∀ i < 2, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi' => by rw [ht, hi.rd]; exact in_rd_left (hs.argIn i hi')
  have rX : ∀ (m : Mem) (v : BitVec 32) (o e : Nat), o + 4 ≤ 256 → e + 4 ≤ 16 →
      (m.writeW (addr B o) v).readW (addr Xp e) 32 = m.readW (addr Xp e) 32 := fun m v o e ho he => by
    rw [addr_add]; exact hs.rD m v ho (by omega)
  unfold loadHead
  repeat rw [WP.block_append_iff (M := isa)]
  refine wp_ldm hi.edi (in_rd (inB _ rfl 48 (by decide))) fun t₁ u₁ => ?_
  refine wp_ldm (B := E) (o := 8) (by rw [u₁.other _ (by decide)]; exact hi.esp) (inA _ u₁.rd 1 (by decide))
    fun t₂ u₂ => WP.block_nil ?_
  have esi₂ : t₂.gpr .esi = Xp := by rw [u₂.other _ (by decide), u₁.gpr]; exact hi.dslot
  have ebp₂ : t₂.gpr .ebp = Yp := by
    rw [u₂.gpr, u₁.mem, ← hs.argY]
    exact hi.frame.readW (hs.argC (by decide) (by decide)) hs.dA (by decide)
  have edi₂ : t₂.gpr .edi = B := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hi.edi]
  have rd₂ : t₂.rd = s.rd := by rw [u₂.rd, u₁.rd]
  have wr₂ : t₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  have m₂ : t₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  -- `Y ⊕ X`.
  refine loadX_wp 0 edi₂ ebp₂ esi₂ (inY _ rd₂ wr₂ _ (by decide)) (inX _ rd₂ wr₂ _ (by decide))
    (inB _ wr₂ _ (by decide)) fun t₃ m₃ g₃ rd₃ wr₃ => ?_
  have k₃ : ∀ r, r ≠ .eax → r ≠ .ebx → t₃.gpr r = t₂.gpr r := g₃
  have rd₃' : t₃.rd = s.rd := rd₃.trans rd₂
  have wr₃' : t₃.wr = s.wr := wr₃.trans wr₂
  have m₃' : t₃.mem = s.mem.writeW (addr B (4 * 0)) (vX s.mem Yp Xp 0) := by rw [m₃, m₂]; rfl
  refine loadX_wp 1 (by rw [k₃ _ (by decide) (by decide), edi₂]) (by rw [k₃ _ (by decide) (by decide), ebp₂])
    (by rw [k₃ _ (by decide) (by decide), esi₂]) (inY _ rd₃' wr₃' _ (by decide)) (inX _ rd₃' wr₃' _ (by decide))
    (inB _ wr₃' _ (by decide)) fun t₄ m₄ g₄ rd₄ wr₄ => ?_
  have k₄ : ∀ r, r ≠ .eax → r ≠ .ebx → t₄.gpr r = t₂.gpr r := fun r h1 h2 => (g₄ r h1 h2).trans (k₃ r h1 h2)
  have rd₄' : t₄.rd = s.rd := rd₄.trans rd₃'
  have wr₄' : t₄.wr = s.wr := wr₄.trans wr₃'
  have m₄' : t₄.mem = (s.mem.writeW (addr B (4 * 0)) (vX s.mem Yp Xp 0)).writeW (addr B (4 * 1))
      (vX s.mem Yp Xp 1) := by
    rw [m₄, m₃', hs.rY _ _ (by decide) (by decide), rX _ _ _ _ (by decide) (by decide)]; rfl
  refine loadX_wp 2 (by rw [k₄ _ (by decide) (by decide), edi₂]) (by rw [k₄ _ (by decide) (by decide), ebp₂])
    (by rw [k₄ _ (by decide) (by decide), esi₂]) (inY _ rd₄' wr₄' _ (by decide)) (inX _ rd₄' wr₄' _ (by decide))
    (inB _ wr₄' _ (by decide)) fun t₅ m₅ g₅ rd₅ wr₅ => ?_
  have k₅ : ∀ r, r ≠ .eax → r ≠ .ebx → t₅.gpr r = t₂.gpr r := fun r h1 h2 => (g₅ r h1 h2).trans (k₄ r h1 h2)
  have rd₅' : t₅.rd = s.rd := rd₅.trans rd₄'
  have wr₅' : t₅.wr = s.wr := wr₅.trans wr₄'
  have m₅' : t₅.mem = ((s.mem.writeW (addr B (4 * 0)) (vX s.mem Yp Xp 0)).writeW (addr B (4 * 1))
      (vX s.mem Yp Xp 1)).writeW (addr B (4 * 2)) (vX s.mem Yp Xp 2) := by
    rw [m₅, m₄', hs.rY _ _ (by decide) (by decide), rX _ _ _ _ (by decide) (by decide),
      hs.rY _ _ (by decide) (by decide), rX _ _ _ _ (by decide) (by decide)]; rfl
  refine loadX_wp 3 (by rw [k₅ _ (by decide) (by decide), edi₂]) (by rw [k₅ _ (by decide) (by decide), ebp₂])
    (by rw [k₅ _ (by decide) (by decide), esi₂]) (inY _ rd₅' wr₅' _ (by decide)) (inX _ rd₅' wr₅' _ (by decide))
    (inB _ wr₅' _ (by decide)) fun t₆ m₆ g₆ rd₆ wr₆ => ?_
  have k₆ : ∀ r, r ≠ .eax → r ≠ .ebx → t₆.gpr r = t₂.gpr r := fun r h1 h2 => (g₆ r h1 h2).trans (k₅ r h1 h2)
  have wr₆' : t₆.wr = s.wr := wr₆.trans wr₅'
  have m₆' : t₆.mem = (((s.mem.writeW (addr B (4 * 0)) (vX s.mem Yp Xp 0)).writeW (addr B (4 * 1))
      (vX s.mem Yp Xp 1)).writeW (addr B (4 * 2)) (vX s.mem Yp Xp 2)).writeW (addr B (4 * 3)) (vX s.mem Yp Xp 3) := by
    rw [m₆, m₅', hs.rY _ _ (by decide) (by decide), rX _ _ _ _ (by decide) (by decide),
      hs.rY _ _ (by decide) (by decide), rX _ _ _ _ (by decide) (by decide),
      hs.rY _ _ (by decide) (by decide), rX _ _ _ _ (by decide) (by decide)]; rfl
  -- `Z := 0`.
  have edi₆ : t₆.gpr .edi = B := by rw [k₆ _ (by decide) (by decide), edi₂]
  refine wp_movi fun t₇ u₇ => ?_
  have edi₇ : t₇.gpr .edi = B := by rw [u₇.other _ (by decide), edi₆]
  refine wp_stm edi₇ (inB _ (by rw [u₇.wr, wr₆']) _ (by decide)) fun t₈ u₈ => ?_
  refine wp_stm (by rw [u₈.gpr]; exact edi₇) (inB _ (by rw [u₈.wr, u₇.wr, wr₆']) _ (by decide)) fun t₉ u₉ => ?_
  refine wp_stm (by rw [u₉.gpr, u₈.gpr]; exact edi₇) (inB _ (by rw [u₉.wr, u₈.wr, u₇.wr, wr₆']) _ (by decide))
    fun t₁₀ u₁₀ => ?_
  refine wp_stm (by rw [u₁₀.gpr, u₉.gpr, u₈.gpr]; exact edi₇)
    (inB _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆']) _ (by decide)) fun t₁₁ u₁₁ => ?_
  have esp₁₁ : t₁₁.gpr .esp = E := by
    rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.other _ (by decide), k₆ _ (by decide) (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hi.esp]
  have rd₁₁ : t₁₁.rd = s.rd := by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅']
  have wr₁₁ : t₁₁.wr = s.wr := by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆']
  have m₁₁ : t₁₁.mem = headMem s.mem B Yp Xp := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.gpr, u₇.mem, m₆']; rfl
  refine wp_ldm (B := E) (o := 4) esp₁₁ (inA _ rd₁₁ 0 (by decide)) fun t₁₂ u₁₂ => WP.block_nil ?_
  refine ⟨by rw [u₁₂.mem, m₁₁], ?_, ?_, by rw [u₁₂.other _ (by decide), esp₁₁], by rw [u₁₂.rd, rd₁₁],
    by rw [u₁₂.wr, wr₁₁]⟩
  · rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.gpr, edi₇]
  · rw [u₁₂.gpr, m₁₁, (hs.headMem_frame s.mem Xp).readW (hs.argC (by decide) (by decide)) (hs.dM hs.aS)
      (by decide), ← hs.argH]
    exact hi.frame.readW (hs.argC (by decide) (by decide)) hs.dA (by decide)

/-- Block `b`'s `Y ⊕ X`, `Z := 0`, `V := H`. -/
theorem load_ok {b : Nat} {s : State} (hi : BInv s₁ Hp Yp Dp B E n b s) (hb : b < n) :
    WP isa (.block load) s fun s' =>
      Inner (blockAt s.mem (Yp.setWidth 64) ^^^ blockAt s.mem ((Dp + BitVec.ofNat 32 (16 * b)).setWidth 64))
        (blockAt s₁.mem (Hp.setWidth 64)) B s' 0 0 s' ∧
      Frame (mRegions B) s.mem s'.mem ∧ s'.gpr .esp = E ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr := by
  have fB := hs.fB; have fH := hs.fH; have fY := hs.fY
  let Xp := Dp + BitVec.ofNat 32 (16 * b)
  have fX : Xp.toNat + 16 ≤ 2 ^ 32 := hs.fX hb
  let x := blockAt s.mem (Yp.setWidth 64) ^^^ blockAt s.mem (Xp.setWidth 64)
  have inH : ∀ (t : State), t.rd = s.rd → t.wr = s.wr → ∀ e, e + 4 ≤ 16 →
      InRegions (t.rd ++ t.wr) (addr Hp e) 4 :=
    fun t h1 h2 e he => by rw [h1, h2, hi.rd]; exact in_rd_left (in_reg hs.hR fH he (by decide))
  have hH : ∀ k < 4, (headMem s.mem B Yp Xp).readW (addr Hp (4 * k)) 32 =
      s₁.mem.readW (addr Hp (4 * k)) 32 := fun k hk => by
    have c : (reg32 Hp 16).Contains (addr Hp (4 * k)) (32 / 8) := reg_contains fH (by omega) (by decide)
    rw [(hs.headMem_frame s.mem Xp).readW c (hs.dM hs.dHS) (by decide)]
    refine hi.frame.readW c (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.dHY
    · exact hs.dHS.sub_right (Region.sub_prefix (by decide))
    · exact hs.dHS.sub_right (part_sub_reg fB (by simp only [dOff]; omega))
  rw [load_eq]
  repeat rw [WP.block_append_iff (M := isa)]
  refine WP.mono (head_ok hs hi hb) fun t ⟨m₀, edi₀, ebp₀, esp₀, rd₀, wr₀⟩ => ?_
  refine vLoad_wp 0 ebp₀ (inH _ rd₀ wr₀ _ (by decide)) fun t₁ a₁ g₁ m₁ rd₁ wr₁ => ?_
  refine vLoad_wp 1 (by rw [g₁ _ (by decide), ebp₀]) (inH _ (by rw [rd₁, rd₀]) (by rw [wr₁, wr₀]) _
    (by decide)) fun t₂ a₂ g₂ m₂ rd₂ wr₂ => ?_
  refine vLoad_wp 2 (by rw [g₂ _ (by decide), g₁ _ (by decide), ebp₀])
    (inH _ (by rw [rd₂, rd₁, rd₀]) (by rw [wr₂, wr₁, wr₀]) _ (by decide)) fun t₃ a₃ g₃ m₃ rd₃ wr₃ => ?_
  refine vLoad_wp 3 (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), ebp₀])
    (inH _ (by rw [rd₃, rd₂, rd₁, rd₀]) (by rw [wr₃, wr₂, wr₁, wr₀]) _ (by decide))
    fun t₄ a₄ g₄ m₄ rd₄ wr₄ => ?_
  have edi₄ : t₄.gpr .edi = B := by
    rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), edi₀]
  have wr₄' : t₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁, wr₀]
  refine wp_movi fun t₅ u₅ => wp_stm (B := B) (by rw [u₅.other _ (by decide), edi₄])
    (by rw [u₅.wr, wr₄', hi.wr]; exact in_reg hs.sW fB (by decide) (by decide)) fun t₆ u₆ => WP.block_nil ?_
  have mh : ∀ {t' : State}, t'.mem = t.mem → t'.mem = headMem s.mem B Yp Xp := fun h => h.trans m₀
  have m₆ : t₆.mem = (headMem s.mem B Yp Xp).writeW (addr B 56) (4 : BitVec 32) := by
    rw [u₆.mem, u₅.gpr, u₅.mem, mh (m₄.trans (m₃.trans (m₂.trans m₁)))]
  have rv : ∀ k < 4, t₆.gpr (vReg k) = bswap (s₁.mem.readW (addr Hp (4 * k)) 32) := by
    intro k hk
    rw [u₆.gpr, u₅.other _ (vReg_ne_esi k), ← hH k hk]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), a₁, mh rfl]
    · rw [g₄ _ (by decide), g₃ _ (by decide), a₂, mh m₁]
    · rw [g₄ _ (by decide), a₃, mh (m₂.trans m₁)]
    · rw [a₄, mh (m₃.trans (m₂.trans m₁))]
  have fit' := fB
  have xv : ∀ w < 4, vX s.mem Yp Xp w = xw x w := by
    intro w hw
    simp only [x, xw_xor, blockAt_words s.mem fY, blockAt_words s.mem fX]
    rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) with rfl | rfl | rfl | rfl <;>
      simp only [vX, xw_cat4_0, xw_cat4_1, xw_cat4_2, xw_cat4_3, Nat.reduceMul]
  have rdM : ∀ w < 4, t₆.mem.readW (addr B (4 * w)) 32 = xw x w := by
    intro w hw
    rw [m₆, ← xv w hw]
    rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) with rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [headMem, rd_wr_ne fit', Mem.readW_writeW_self32, Nat.reduceMul]
  refine ⟨⟨fB, by rw [u₆.wr, u₅.wr, wr₄']; rw [hi.wr]; exact hs.sW, ?_, ?_, fun j h1 h2 => ?_, ?_,
    by rw [u₆.gpr, u₅.other _ (by decide), edi₄], rfl, rfl, rfl, Frame.refl _ _⟩, ?_, ?_, ?_, ?_⟩
  · rw [mulSteps_zero]
    refine Prod.ext ?_ ?_
    · show zOf t₆.mem B = 0
      rw [m₆]
      simp (disch := decide) only [zOf, zw, zOff, headMem, rd_wr_ne fit', Mem.readW_writeW_self32,
        Nat.reduceMul, Nat.reduceAdd]
      decide
    · show vOf t₆ = _
      rw [blockAt_words s₁.mem fH]
      simp only [vOf]
      rw [show Reg.eax = vReg 0 from rfl, show Reg.ebx = vReg 1 from rfl, show Reg.ecx = vReg 2 from rfl,
        show Reg.edx = vReg 3 from rfl, rv 0 (by decide), rv 1 (by decide), rv 2 (by decide), rv 3 (by decide)]
  · rw [BitVec.shiftLeft_zero, show (0 : Nat) = 4 * 0 from rfl, rdM 0 (by decide)]
  · rw [rdM j (by omega), Nat.zero_add]
  · rw [m₆]; exact Mem.readW_writeW_self32 _ _ _
  · rw [m₆]
    exact (hs.headMem_frame s.mem Xp).writeW (r := ⟨addr B wcOff, 8⟩) (by simp) _
      (part_contains fB (by simp only [wcOff]; omega) (by simp only [wcOff]; omega)
        (by simp only [wcOff]; omega) (by decide))
  · rw [u₆.gpr, u₅.other _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide),
      g₁ _ (by decide), esp₀]
  · rw [u₆.rd, u₅.rd, rd₄, rd₃, rd₂, rd₁, rd₀, hi.rd]
  · rw [u₆.wr, u₅.wr, wr₄', hi.wr]

theorem zStore_wp {s : State} {P : State → Prop} (k : Nat) (hk : k < 4) (hb : s.gpr .edi = B)
    (hy : s.gpr .esi = Yp) (hwY : reg32 Yp 16 ∈ s.wr) (hwB : reg32 B 256 ∈ s.wr)
    (h : ∀ s', s'.mem = s.mem.writeW (addr Yp (4 * k)) (bswap (zw s.mem B k)) →
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (zStore k)) s P := by
  refine wp_ldm hb (in_rd (in_reg hwB hs.fB (by simp only [zOff]; omega) (by decide))) fun s₁ u₁ => ?_
  refine wp_bswap fun s₂ u₂ => wp_stm (B := Yp) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hy])
    (by rw [u₂.wr, u₁.wr]; exact in_reg hwY hs.fY (by omega) (by decide)) fun s₃ u₃ => WP.block_nil ?_
  exact h s₃ (by rw [u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem])
    (fun r hr => by rw [u₃.gpr, u₂.other r hr, u₁.other r hr]) (by rw [u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₃.wr, u₂.wr, u₁.wr])

/-- `Y := Z`, and on to the next block (ZF is set after the last one). -/
theorem store_ok {b : Nat} {s s₃ : State} (hi : BInv s₁ Hp Yp Dp B E n b s) (hb : b < n)
    (F : Frame (mRegions B) s.mem s₃.mem) (edi₃ : s₃.gpr .edi = B) (esp₃ : s₃.gpr .esp = E)
    (rd₃ : s₃.rd = s₁.rd) (wr₃ : s₃.wr = s₁.wr)
    (hz : zOf s₃.mem B = mul (blockAt s.mem (Yp.setWidth 64) ^^^
      blockAt s.mem ((Dp + BitVec.ofNat 32 (16 * b)).setWidth 64)) (blockAt s₁.mem (Hp.setWidth 64))) :
    WP isa (.block store) s₃ fun s' =>
      s'.zf = some (decide (n - (b + 1) = 0)) ∧ BInv s₁ Hp Yp Dp B E n (b + 1) s' := by
  have fB := hs.fB; have fY := hs.fY; have fD := hs.fD
  have hwY : reg32 Yp 16 ∈ s₃.wr := by rw [wr₃]; exact hs.yW
  have hwB : reg32 B 256 ∈ s₃.wr := by rw [wr₃]; exact hs.sW
  -- The slots of the data pointer and the count, and the arguments, are as in `s`.
  have slot : ∀ o, 48 ≤ o → o + 4 ≤ 56 → s₃.mem.readW (addr B o) 32 = s.mem.readW (addr B o) 32 :=
    fun o h1 h2 => F.readW (r := ⟨addr B o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show Region.Disjoint _ ⟨B.setWidth 64, 32⟩
        rw [← addr_zero]; exact part_disj fB (by omega) (by decide) (.inr (by omega))
      · exact part_disj fB (by omega) (by simp only [wcOff]; omega) (.inl (by simp only [wcOff]; omega)))
      (by decide)
  rw [store_eq]
  repeat rw [WP.block_append_iff (M := isa)]
  refine wp_ldm (B := E) (o := 8) esp₃ (by rw [rd₃]; exact in_rd_left (hs.argIn 1 (by decide)))
    fun t₁ u₁ => WP.block_nil ?_
  have esi₁ : t₁.gpr .esi = Yp := by
    rw [u₁.gpr, F.readW (hs.argC (by decide) (by decide)) (hs.dM hs.aS) (by decide), ← hs.argY]
    exact hi.frame.readW (hs.argC (by decide) (by decide)) hs.dA (by decide)
  have edi₁ : t₁.gpr .edi = B := by rw [u₁.other _ (by decide), edi₃]
  refine zStore_wp hs 0 (by decide) edi₁ esi₁ (by rw [u₁.wr]; exact hwY) (by rw [u₁.wr]; exact hwB)
    fun t₂ m₂ g₂ rd₂ wr₂ => ?_
  refine zStore_wp hs 1 (by decide) (by rw [g₂ _ (by decide), edi₁]) (by rw [g₂ _ (by decide), esi₁])
    (by rw [wr₂, u₁.wr]; exact hwY) (by rw [wr₂, u₁.wr]; exact hwB) fun t₃ m₃ g₃ rd₃' wr₃' => ?_
  refine zStore_wp hs 2 (by decide) (by rw [g₃ _ (by decide), g₂ _ (by decide), edi₁])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), esi₁]) (by rw [wr₃', wr₂, u₁.wr]; exact hwY)
    (by rw [wr₃', wr₂, u₁.wr]; exact hwB) fun t₄ m₄ g₄ rd₄ wr₄ => ?_
  refine zStore_wp hs 3 (by decide) (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), edi₁])
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), esi₁])
    (by rw [wr₄, wr₃', wr₂, u₁.wr]; exact hwY) (by rw [wr₄, wr₃', wr₂, u₁.wr]; exact hwB)
    fun t₅ m₅ g₅ rd₅ wr₅ => ?_
  have m₅' : t₅.mem = yMem s₃.mem B Yp := by
    rw [m₅, m₄, m₃, m₂, u₁.mem]
    simp only [zw, zOff, hs.rB _ _ (by decide : 16 + 4 * 1 + 4 ≤ 256) (by decide : 4 * 0 + 4 ≤ 16),
      hs.rB _ _ (by decide : 16 + 4 * 2 + 4 ≤ 256) (by decide : 4 * 0 + 4 ≤ 16),
      hs.rB _ _ (by decide : 16 + 4 * 2 + 4 ≤ 256) (by decide : 4 * 1 + 4 ≤ 16),
      hs.rB _ _ (by decide : 16 + 4 * 3 + 4 ≤ 256) (by decide : 4 * 0 + 4 ≤ 16),
      hs.rB _ _ (by decide : 16 + 4 * 3 + 4 ≤ 256) (by decide : 4 * 1 + 4 ≤ 16),
      hs.rB _ _ (by decide : 16 + 4 * 3 + 4 ≤ 256) (by decide : 4 * 2 + 4 ≤ 16)]
    rfl
  have yB : ∀ o, o + 4 ≤ 256 → (yMem s₃.mem B Yp).readW (addr B o) 32 = s₃.mem.readW (addr B o) 32 :=
    fun o ho => by
      simp only [yMem]
      rw [hs.rB _ _ ho (by decide), hs.rB _ _ ho (by decide), hs.rB _ _ ho (by decide), hs.rB _ _ ho (by decide)]
  have edi₅ : t₅.gpr .edi = B := by rw [g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), edi₁]
  have wr₅' : t₅.wr = s₃.wr := by rw [wr₅, wr₄, wr₃', wr₂, u₁.wr]
  have inB : ∀ (t : State), t.wr = s₃.wr → ∀ o, o + 4 ≤ 256 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hwB fB ho (by decide)
  refine wp_ldm edi₅ (in_rd (inB _ wr₅' 48 (by decide))) fun t₆ u₆ => wp_addi fun t₇ u₇ => ?_
  refine wp_stm (B := B) (by rw [u₇.other _ (by decide), u₆.other _ (by decide), edi₅])
    (inB _ (by rw [u₇.wr, u₆.wr, wr₅']) 48 (by decide)) fun t₈ u₈ => ?_
  refine wp_ldm (by rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), edi₅])
    (in_rd (inB _ (by rw [u₈.wr, u₇.wr, u₆.wr, wr₅']) 52 (by decide))) fun t₉ u₉ => wp_subi fun t₁₀ u₁₀ _ z₁₀ => ?_
  refine wp_stm (B := B) (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr,
      u₇.other _ (by decide), u₆.other _ (by decide), edi₅])
    (inB _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅']) 52 (by decide)) fun t₁₁ u₁₁ => WP.block_nil ?_
  have fit' := fB
  have d₇ : t₇.gpr .esi = Dp + BitVec.ofNat 32 (16 * (b + 1)) := by
    rw [u₇.gpr, u₆.gpr, m₅', yB _ (by decide), slot 48 (by decide) (by decide)]
    rw [show (48 : Nat) = dOff from rfl, hi.dslot, BitVec.add_assoc]
    congr 1
    rw [show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add, Nat.mul_succ]
  have n₉ : t₉.gpr .esi = BitVec.ofNat 32 (n - b) := by
    rw [u₉.gpr, u₈.mem, u₇.mem, u₆.mem, m₅', rd_wr_ne fit' _ _ (by decide) (by decide) (by decide) (by decide)
      (by decide), yB _ (by decide), slot 52 (by decide) (by decide)]
    exact hi.nslot
  let M := ((yMem s₃.mem B Yp).writeW (addr B 48) (Dp + BitVec.ofNat 32 (16 * (b + 1)))).writeW (addr B 52)
    (BitVec.ofNat 32 (n - (b + 1)))
  have m₁₁ : t₁₁.mem = M := by
    rw [u₁₁.mem, u₁₀.gpr, n₉, ofNat_pred (by omega), Nat.sub_sub, u₁₀.mem, u₉.mem, u₈.mem, d₇, u₇.mem, u₆.mem,
      m₅']
  have fY' := fY
  have hbn : 16 * b + 16 ≤ 16 * n := by omega
  -- The new `Y`.
  have hy : blockAt M (Yp.setWidth 64) = zOf s₃.mem B := by
    rw [blockAt_words M fY]
    simp only [M]
    rw [hs.rY _ _ (by decide) (by decide), hs.rY _ _ (by decide) (by decide), hs.rY _ _ (by decide) (by decide),
      hs.rY _ _ (by decide) (by decide), hs.rY _ _ (by decide) (by decide), hs.rY _ _ (by decide) (by decide),
      hs.rY _ _ (by decide) (by decide), hs.rY _ _ (by decide) (by decide)]
    simp (disch := decide) only [yMem, rd_wr_ne fY', Mem.readW_writeW_self32, Nat.reduceMul, bswap_bswap]
    rfl
  -- The block `X`.
  have hx : blockAt s.mem ((Dp + BitVec.ofNat 32 (16 * b)).setWidth 64) =
      blockAt s₁.mem (Dp.setWidth 64 + BitVec.ofNat 64 (16 * b)) := by
    rw [← addr_eq (by omega)]
    refine Proof.Gcm.blockAt_congr fun i hi' => ?_
    refine hi.frame.bytes (R := ⟨addr Dp (16 * b), 16⟩) (fun r hr => ?_) (by show 16 ≤ 2 ^ 64; decide) hi'
    have d : Region.Disjoint ⟨addr Dp (16 * b), 16⟩ (reg32 B 256) := hs.dDS.sub_left (part_sub_reg fD hbn)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hs.dYD.sub_right (part_sub_reg fD hbn)).symm
    · exact d.sub_right (Region.sub_prefix (by decide))
    · exact d.sub_right (part_sub_reg fB (by simp only [dOff]; omega))
  have fr : Frame (bRegions Yp B) s₁.mem M := by
    have f₃ : Frame (bRegions Yp B) s₁.mem s₃.mem := hi.frame.trans (F.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨reg32 B 32, by simp, fun _ h => h⟩
      · exact ⟨⟨addr B dOff, 16⟩, by simp, part_sub fB (by simp only [dOff]; omega)
          (by simp only [dOff, wcOff]; omega) (by simp only [dOff, wcOff]; omega)⟩)
    have hY : reg32 Yp 16 ∈ bRegions Yp B := List.mem_cons_self ..
    have hD : (⟨addr B dOff, 16⟩ : Region) ∈ bRegions Yp B := by simp
    have cY : ∀ k < 4, (reg32 Yp 16).Contains (addr Yp (4 * k)) (32 / 8) := fun k hk =>
      reg_contains fY (by omega) (by decide)
    have cD : ∀ o, 48 ≤ o → o + 4 ≤ 64 → (⟨addr B dOff, 16⟩ : Region).Contains (addr B o) (32 / 8) :=
      fun o h1 h2 => part_contains fB (by simp only [dOff]; omega) (by simp only [dOff]; omega)
        (by simp only [dOff]; omega) (by decide)
    exact (((((f₃.writeW hY _ (cY 0 (by decide))).writeW hY _ (cY 1 (by decide))).writeW hY _
      (cY 2 (by decide))).writeW hY _ (cY 3 (by decide))).writeW hD _ (cD 48 (by decide) (by decide))).writeW hD _
      (cD 52 (by decide) (by decide))
  refine ⟨?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₁₁]; exact fr⟩
  · rw [u₁₁.zf, z₁₀, n₉, ofNat_pred (by omega), ofNat_beq_zero (by omega), Nat.sub_sub]
  · rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), edi₅]
  · rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide),
      u₁.other _ (by decide), esp₃]
  · rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅, rd₄, rd₃', rd₂, u₁.rd, rd₃]
  · rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅', wr₃]
  · rw [m₁₁]; simp (disch := decide) only [M, dOff, rd_wr_ne fit', Mem.readW_writeW_self32]
  · rw [m₁₁]; simp only [M, nOff, Mem.readW_writeW_self32]
  · rw [m₁₁, hy, hz, ghashFrom_blocksAt_succ, ← hi.y, hx]

/-- One block. -/
theorem body_ok {b : Nat} {s : State} (hi : BInv s₁ Hp Yp Dp B E n b s) (hb : b < n) :
    WP isa body s fun s' => s'.zf = some (decide (n - (b + 1) = 0)) ∧ BInv s₁ Hp Yp Dp B E n (b + 1) s' := by
  unfold body
  refine WP.seq (WP.mono (load_ok hs hi hb) fun s₂ ⟨hin, F₂, esp₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (mul_ok hin) fun s₃ hd => ?_)
  refine store_ok hs hi hb (F₂.trans hd.frame) hd.edi (hd.esp.trans esp₂) (hd.rd.trans rd₂) (hd.wr.trans wr₂) ?_
  rw [mul_eq, ← hd.zv]

/-- The loop over the blocks. -/
theorem blocks_ok {s : State} (hi : BInv s₁ Hp Yp Dp B E n 0 s) (hn : 0 < n) :
    WP isa (.loop body .ne) s (BInv s₁ Hp Yp Dp B E n n) := by
  refine WP.loop (M := isa) (fun k s => ∃ b, k = n - b ∧ b < n ∧ BInv s₁ Hp Yp Dp B E n b s)
    (fun k s ⟨b, hk, hb, hs'⟩ => WP.mono (body_ok hs hs' hb) fun s' ⟨z, d⟩ => ?_) n s ⟨0, rfl, hn, hi⟩
  by_cases hl : b + 1 = n
  · refine .inl ⟨by simp [X86.eval, z, hl], ?_⟩
    rw [hl] at d; exact d
  · exact .inr ⟨by simp [X86.eval, z]; omega, n - (b + 1), by omega, b + 1, rfl, by omega, d⟩

end

/-! ## The prologue and the epilogue -/

/-- After the prologue. -/
structure GP1 (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  edi : s.gpr .edi = sP s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  zf : s.zf = some (decide (nBlk s₀ = 0))
  dslot : s.mem.readW (addr (sP s₀) dOff) 32 = dP s₀
  nslot : s.mem.readW (addr (sP s₀) nOff) 32 = arg s₀ 3
  frame : Frame [⟨addr (sP s₀) 32, 24⟩] s₀.mem s.mem
  saved : ∀ p ∈ savedRegs, s.mem.readW (addr (sP s₀) p.2) 32 = s₀.gpr p.1

theorem prologue_eq : prologue = ([.mov .eax (.mem (at_ .esp 20)), .store (at_ .eax 32) .ebx,
    .store (at_ .eax 36) .esi, .store (at_ .eax 40) .edi, .store (at_ .eax 44) .ebp, .mov .edi (.reg .eax),
    .mov .eax (.mem (at_ .esp 12)), .store (at_ .edi 48) .eax, .mov .eax (.mem (at_ .esp 16)),
    .store (at_ .edi 52) .eax, .alu .test .eax (.reg .eax)] : List Instr) := rfl

theorem argC {s₀ : State} (hp : GPre s₀) {i : Nat} (hi : i < 5) :
    (aR s₀).Contains (addr (s₀.gpr .esp) (4 + 4 * i)) 4 := by
  show (⟨addr (s₀.gpr .esp) 4, 20⟩ : Region).Contains _ _
  exact part_contains (N := 24) (by have := hp.fSp; omega) (by decide) (by omega) (by omega) (by decide)

theorem prologue_ok {s₀ : State} (hp : GPre s₀) : WP isa (.block prologue) s₀ (GP1 s₀) := by
  have fB : (sP s₀).toNat + 256 ≤ 2 ^ 32 := hp.fS
  let B := sP s₀
  let E := s₀.gpr .esp
  have hwB : reg32 B 256 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hrA : aR s₀ ∈ s₀.rd := by rw [hp.rd]; simp
  have argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 5, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨aR s₀, List.mem_append_left _ (ht ▸ hrA), argC hp hi⟩
  have bIn : ∀ (t : State), t.wr = s₀.wr → ∀ o, o + 4 ≤ 256 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact in_reg hwB fB ho (by decide)
  have hm : (⟨addr B 32, 24⟩ : Region) ∈ [(⟨addr B 32, 24⟩ : Region)] := List.mem_singleton_self _
  have cB : ∀ o, 32 ≤ o → o + 4 ≤ 56 → (⟨addr B 32, 24⟩ : Region).Contains (addr B o) (32 / 8) :=
    fun o h1 h2 => part_contains fB (by decide) h1 (by omega) (by decide)
  have dA : ∀ r ∈ [(⟨addr B 32, 24⟩ : Region)], (aR s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.aS.sub_right (part_sub_reg fB (by decide))
  rw [prologue_eq]
  refine wp_ldm (B := E) (o := 20) rfl (argIn _ rfl 4 (by decide)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = B := by rw [u₁.gpr]; rfl
  refine wp_stm e₁ (bIn _ u₁.wr 32 (by decide)) fun s₂ u₂ => ?_
  refine wp_stm (by rw [u₂.gpr]; exact e₁) (bIn _ (by rw [u₂.wr, u₁.wr]) 36 (by decide)) fun s₃ u₃ => ?_
  refine wp_stm (by rw [u₃.gpr, u₂.gpr]; exact e₁) (bIn _ (by rw [u₃.wr, u₂.wr, u₁.wr]) 40 (by decide))
    fun s₄ u₄ => ?_
  refine wp_stm (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁)
    (bIn _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 44 (by decide)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => ?_
  have g₆ : ∀ r, r ≠ .eax → r ≠ .edi → s₆.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₆.other r h2, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r h1]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have edi₆ : s₆.gpr .edi = B := by rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁
  have esp₆ : s₆.gpr .esp = E := g₆ _ (by decide) (by decide)
  let M := (((s₀.mem.writeW (addr B 32) (s₀.gpr .ebx)).writeW (addr B 36) (s₀.gpr .esi)).writeW
    (addr B 40) (s₀.gpr .edi)).writeW (addr B 44) (s₀.gpr .ebp)
  have m₆ : s₆.mem = M := by
    simp only [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr]
    rw [u₁.other .ebx (by decide), u₁.other .esi (by decide), u₁.other .edi (by decide),
      u₁.other .ebp (by decide), u₁.mem]
  have f₆ : Frame [⟨addr B 32, 24⟩] s₀.mem s₆.mem := by
    rw [m₆]
    exact ((((Frame.refl _ _).writeW hm _ (cB 32 (by decide) (by decide))).writeW hm _
      (cB 36 (by decide) (by decide))).writeW hm _ (cB 40 (by decide) (by decide))).writeW hm _
      (cB 44 (by decide) (by decide))
  refine wp_ldm (B := E) (o := 12) esp₆ (argIn _ rd₆ 2 (by decide)) fun s₇ u₇ => ?_
  refine wp_stm (B := B) (by rw [u₇.other _ (by decide), edi₆]) (bIn _ (by rw [u₇.wr, wr₆]) 48 (by decide))
    fun s₈ u₈ => ?_
  have f₈ : Frame [⟨addr B 32, 24⟩] s₀.mem s₈.mem := by
    rw [u₈.mem, u₇.mem]; exact f₆.writeW hm _ (cB 48 (by decide) (by decide))
  refine wp_ldm (B := E) (o := 16) (by rw [u₈.gpr, u₇.other _ (by decide), esp₆])
    (argIn _ (by rw [u₈.rd, u₇.rd, rd₆]) 3 (by decide)) fun s₉ u₉ => ?_
  refine wp_stm (B := B) (by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), edi₆])
    (bIn _ (by rw [u₉.wr, u₈.wr, u₇.wr, wr₆]) 52 (by decide)) fun s₁₀ u₁₀ => ?_
  refine wp_test fun s₁₁ u₁₁ z₁₁ => WP.block_nil ?_
  have a₇ : s₇.gpr .eax = dP s₀ := by
    rw [u₇.gpr]; exact f₆.readW (argC hp (i := 2) (by decide)) dA (by decide)
  have a₉ : s₉.gpr .eax = arg s₀ 3 := by
    rw [u₉.gpr]; exact f₈.readW (argC hp (i := 3) (by decide)) dA (by decide)
  have fit' : B.toNat + 256 ≤ 2 ^ 32 := fB
  let M' := (M.writeW (addr B 48) (dP s₀)).writeW (addr B 52) (arg s₀ 3)
  have m₁₁ : s₁₁.mem = M' := by
    rw [u₁₁.mem, u₁₀.mem, a₉, u₉.mem, u₈.mem, a₇, u₇.mem, m₆]
  refine ⟨?_, ?_, by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆], by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆],
    ?_, ?_, ?_, ?_, fun p hp' => ?_⟩
  · rw [u₁₁.gpr, u₁₀.gpr, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), esp₆]
  · rw [u₁₁.gpr, u₁₀.gpr, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), edi₆]
  · rw [z₁₁, u₁₀.gpr, a₉, BitVec.and_self]
    by_cases h : arg s₀ 3 = 0
    · simp [h, nBlk]
    · have : (arg s₀ 3).toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      rw [show (arg s₀ 3 == 0) = false from beq_eq_false_iff_ne.mpr h]
      simp [nBlk, this]
  · rw [m₁₁]; show M'.readW (addr B 48) 32 = _
    simp (disch := decide) only [M', rd_wr_ne fit', Mem.readW_writeW_self32]
  · rw [m₁₁]; show M'.readW (addr B 52) 32 = _
    simp only [M', Mem.readW_writeW_self32]
  · rw [m₁₁]
    have := (f₆.writeW hm (dP s₀) (cB 48 (by decide) (by decide))).writeW hm (arg s₀ 3) (cB 52 (by decide) (by decide))
    rwa [m₆] at this
  · rw [m₁₁]
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> show M'.readW (addr B _) 32 = _ <;>
    simp (disch := decide) only [M', M, rd_wr_ne fit', Mem.readW_writeW_self32]

theorem restore_ok {s : State} {B : BitVec 32} (hb : s.gpr .edi = B) (hfit : B.toNat + 256 ≤ 2 ^ 32)
    (hw : reg32 B 256 ∈ s.wr) :
    WP isa (.block restore) s fun s' =>
      (∀ p ∈ savedRegs, s'.gpr p.1 = s.mem.readW (addr B p.2) 32) ∧
      (∀ r, r ∉ [Reg.ebx, .esi, .edi, .ebp] → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  have hin : ∀ (t : State), t.rd = s.rd → t.wr = s.wr → ∀ o, o + 4 ≤ 256 →
      InRegions (t.rd ++ t.wr) (addr B o) 4 :=
    fun t h1 h2 o ho => by rw [h1, h2]; exact in_rd (in_reg hw hfit ho (by decide))
  refine wp_ldm hb (hin _ rfl rfl 32 (by decide)) fun s₁ u₁ => ?_
  refine wp_ldm (by rw [u₁.other _ (by decide)]; exact hb) (hin _ u₁.rd u₁.wr 36 (by decide)) fun s₂ u₂ => ?_
  refine wp_ldm (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (hin _ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) 44 (by decide)) fun s₃ u₃ => ?_
  refine wp_ldm (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (hin _ (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr]) 40 (by decide))
    fun s₄ u₄ => WP.block_nil ⟨fun p hp => ?_, fun r hr => ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem]
    · rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other _ hr.2.2.1, u₃.other _ hr.2.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]

/-! ## The whole function -/

theorem blocksAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < 16 * n, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    blocksAt m' p n = blocksAt m p n := by
  unfold blocksAt
  refine List.map_congr_left fun i hi => Proof.Gcm.blockAt_congr fun j hj => ?_
  rw [List.mem_range] at hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

theorem gh_correct {s₀ : State} (hp : GPre s₀) :
    WP isa Impl.Gcm.X86.ghash s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Gcm.ghashX86.post s₀ s' := by
  let Hp := hP s₀
  let Yp := yP s₀
  let Dp := dP s₀
  let B := sP s₀
  let E := s₀.gpr .esp
  let n := nBlk s₀
  have fH : Hp.toNat + 16 ≤ 2 ^ 32 := hp.fH
  have fY : Yp.toNat + 16 ≤ 2 ^ 32 := hp.fY
  have fD : Dp.toNat + 16 * n ≤ 2 ^ 32 := hp.fD
  have fB : B.toNat + 256 ≤ 2 ^ 32 := hp.fS
  have fE : E.toNat + 24 ≤ 2 ^ 32 := hp.fSp
  unfold Impl.Gcm.X86.ghash
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have d₁ : ∀ {R : Region}, R.Disjoint (sR s₀) → ∀ r ∈ [(⟨addr B 32, 24⟩ : Region)], R.Disjoint r :=
    fun hR r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hR.sub_right (part_sub_reg fB (by decide))
  have aSub : Region.Sub ⟨addr E 4, 8⟩ (aR s₀) := Region.sub_prefix (by decide)
  have hs : BSetup s₁ Hp Yp Dp B E n :=
    { hR := by rw [h₁.rd, hp.rd]; exact List.mem_cons_self ..
      dR := by rw [h₁.rd, hp.rd]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      yW := by rw [h₁.wr, hp.wr]; exact List.mem_cons_self ..
      sW := by rw [h₁.wr, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
      fH, fY, fD, fB, fE
      dHY := hp.dHY, dHS := hp.dHS, dYD := hp.dYD, dYS := hp.dYS, dDS := hp.dDS
      argIn := fun i hi => ⟨aR s₀, by rw [h₁.rd, hp.rd]; simp, argC hp (by omega)⟩
      argH := h₁.frame.readW (argC hp (i := 0) (by decide)) (d₁ hp.aS) (by decide)
      argY := h₁.frame.readW (argC hp (i := 1) (by decide)) (d₁ hp.aS) (by decide)
      aY := hp.aY.sub_left aSub
      aS := hp.aS.sub_left aSub }
  have bi : BInv s₁ Hp Yp Dp B E n 0 s₁ :=
    { hb := Nat.zero_le _
      edi := h₁.edi
      esp := h₁.esp
      rd := rfl
      wr := rfl
      dslot := by
        rw [Nat.mul_zero, show Dp + BitVec.ofNat 32 0 = Dp from BitVec.add_zero _]; exact h₁.dslot
      nslot := by rw [Nat.sub_zero]; rw [h₁.nslot]; simp [n]
      y := rfl
      frame := Frame.refl _ _ }
  refine WP.seq (WP.mono (Q := BInv s₁ Hp Yp Dp B E n n) (WP.ite (decide (n = 0))
    (by simp only [X86.eval, h₁.zf]; rfl) (fun h => WP.block_nil ?_) (fun h => blocks_ok hs bi ?_)) fun s₄ h₄ => ?_)
  · have : n = 0 := by simpa using h
    rw [this] at bi ⊢; exact bi
  · have : n ≠ 0 := by simpa using h
    omega
  refine WP.mono (restore_ok h₄.edi fB (by rw [h₄.wr]; exact hs.sW)) fun s₅ ⟨sv₅, o₅, m₅⟩ => ?_
  -- What the whole function writes.
  have F : Frame [reg32 Yp 16, reg32 B 256] s₀.mem s₄.mem :=
    (h₁.frame.sub fun r hr => ⟨reg32 B 256, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by decide)⟩).trans
    (h₄.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨reg32 Yp 16, by simp, fun _ h => h⟩
      · exact ⟨reg32 B 256, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨reg32 B 256, by simp, part_sub_reg fB (by simp only [dOff]; omega)⟩)
  have saved : ∀ p ∈ savedRegs, s₄.mem.readW (addr B p.2) 32 = s₀.gpr p.1 := by
    intro p hp'
    have h2 : 32 ≤ p.2 ∧ p.2 + 4 ≤ 48 := by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> decide
    rw [← h₁.saved p hp']
    exact h₄.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.dYS.sub_right (part_sub_reg fB (by omega))).symm
      · show Region.Disjoint _ ⟨B.setWidth 64, 32⟩
        rw [← addr_zero]; exact part_disj fB (by omega) (by decide) (.inr (by omega))
      · exact part_disj fB (by omega) (by simp only [dOff]; omega) (.inl (by simp only [dOff]; omega)))
      (by decide)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [sv₅ (.ebx, 32) (by simp [savedRegs]), saved (.ebx, 32) (by simp [savedRegs])]
    · rw [sv₅ (.esi, 36) (by simp [savedRegs]), saved (.esi, 36) (by simp [savedRegs])]
    · rw [sv₅ (.edi, 40) (by simp [savedRegs]), saved (.edi, 40) (by simp [savedRegs])]
    · rw [sv₅ (.ebp, 44) (by simp [savedRegs]), saved (.ebp, 44) (by simp [savedRegs])]
    · rw [o₅ _ (by simp), h₄.esp]
  · rw [m₅]
    exact F.readW (r := rR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.rY
      · exact hp.rS) (by decide)
  · show blockAt s₅.mem (Yp.setWidth 64) =
      ghashFrom (blockAt s₀.mem (Hp.setWidth 64)) (blockAt s₀.mem (Yp.setWidth 64))
        (blocksAt s₀.mem (Dp.setWidth 64) n)
    have eB : ∀ {R : Region}, R.Disjoint (sR s₀) → R.len ≤ 2 ^ 64 → ∀ i < R.len,
        s₁.mem (R.base + BitVec.ofNat 64 i) = s₀.mem (R.base + BitVec.ofNat 64 i) :=
      fun hR hl i hi => h₁.frame.bytes (d₁ hR) hl hi
    rw [m₅, h₄.y]
    rw [Proof.Gcm.blockAt_congr (m := s₀.mem) (m' := s₁.mem) (p := Hp.setWidth 64)
        fun i hi => eB (R := hR s₀) hp.dHS (by show 16 ≤ 2 ^ 64; decide) i hi,
      Proof.Gcm.blockAt_congr (m := s₀.mem) (m' := s₁.mem) (p := Yp.setWidth 64)
        fun i hi => eB (R := yR s₀) hp.dYS (by show 16 ≤ 2 ^ 64; decide) i hi,
      blocksAt_congr (m := s₀.mem) (m' := s₁.mem) (p := Dp.setWidth 64)
        fun i hi => eB (R := dR s₀) hp.dDS (by show 16 * n ≤ 2 ^ 64; omega) i hi]

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0, 0x4000` at `0x8004`. -/
def ghSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30
  else if a = 0x8015 then 0x40 else 0

/-- A state satisfying the precondition (with no data). -/
def ghSat : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ghSatMem
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩]

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashX86.pre s) :
    ∃ t s', Exec isa Impl.Gcm.X86.ghash s t s' ∧ abiPreserved s s' ∧ Proof.Gcm.ghashX86.post s s' :=
  (gh_correct (GPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem ghash_verified :
    Verified X86.target Impl.Gcm.X86.ghash (Spec.Gcm.ghashContract X86.abi) :=
  Verified.of_correct ghash_correct ghash_ct
    (by
      have a0 : arg ghSat 0 = 0x1000 := by decide
      have a1 : arg ghSat 1 = 0x2000 := by decide
      have a2 : arg ghSat 2 = 0x3000 := by decide
      have a3 : arg ghSat 3 = 0 := by decide
      have a4 : arg ghSat 4 = 0x4000 := by decide
      have e : argAddr ghSat 0 = 0x8004 := by decide
      have esp : ghSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Gcm.ghashX86] [a0, a1, a2, a3, a4, e, esp] using ghSat)

end VG.Proof.Gcm.X86
