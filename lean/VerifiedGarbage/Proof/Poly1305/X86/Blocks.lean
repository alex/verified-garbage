import VerifiedGarbage.Proof.Poly1305.X86.Run
import VerifiedGarbage.Proof.Poly1305.X86.Contract
import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# Poly1305 on x86 (32-bit): `blocks`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

/-! ## Common to `blocks`, `update` and `finalize` -/

section
variable (s₀ : State)
/-- The state, on entry. -/
abbrev stp : BitVec 32 := arg s₀ 0
/-- The accumulator on entry. -/
abbrev A0 : Nat := leNum (bytesAt s₀.mem ((stp s₀).setWidth 64) 24)
/-- The clamped `r`. -/
abbrev Rn : Nat :=
  rval (r0v s₀.mem (stp s₀)) (qv s₀.mem (stp s₀) 1) (qv s₀.mem (stp s₀) 2) (qv s₀.mem (stp s₀) 3)
/-- The return address's region. -/
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩
end

theorem arg0_eq (s : State) : s.mem.readW (addr (s.gpr .esp) 4) 32 = arg s 0 := rfl

theorem argAddr_eq (s : State) (i : Nat) : argAddr s i = addr (s.gpr .esp) (4 + 4 * i) := rfl

/-- An argument slot's address, in the argument region. -/
theorem arg_contains {s : State} {n : Nat} (hfit : (s.gpr .esp).toNat + 4 + n ≤ 2 ^ 32) {i : Nat}
    (hi : 4 * i + 4 ≤ n) : (⟨argAddr s 0, n⟩ : Region).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4 :=
  sub_contains (x := s.gpr .esp) (a := 4) (k := n) (by omega) (by omega) (by omega) (by omega)

/-- The key (words 6 to 13) is unchanged since entry. -/
theorem key_same {m m' : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
    (h : ∀ k, 6 ≤ k → k < 14 → words m' st k = words m st k) :
    bytesAt m' (st.setWidth 64 + 24) 32 = bytesAt m (st.setWidth 64 + 24) 32 := by
  show bytesAt m' _ (4 * 8) = bytesAt m _ (4 * 8)
  refine bytesAt_congr_words fun k hk => BitVec.eq_of_toNat_eq ?_
  have := h (6 + k) (by omega) (by omega)
  simp only [words, wv, wd] at this
  rw [show (24 : Addr) = BitVec.ofNat 64 24 from rfl, add_ofNat_add, ← addr_eq (by omega),
    show 24 + 4 * k = 4 * (6 + k) by omega]
  exact this

/-- The clamped `r` of the key on entry. -/
theorem clamp_key (m : Mem) {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) :
    clamp (leNum ((bytesAt m (st.setWidth 64 + 24) 32).take 16)) =
      rval (r0v m st) (qv m st 1) (qv m st 2) (qv m st 3) := by
  rw [show bytesAt m (st.setWidth 64 + 24) 32 = bytesAt m (st.setWidth 64 + 24) (16 + 16) from rfl,
    Poly1305.bytesAt_add, List.take_left' (Poly1305.length_bytesAt _ _ _),
    leNum_bytesAt_16, show (24 : Addr) = BitVec.ofNat 64 24 from rfl]
  rw [w32_off hfit (by omega), w32_off hfit (by omega), w32_off hfit (by omega), w32_off hfit (by omega)]
  have e : ∀ k, words m st k = wv m st (4 * k) := fun _ => rfl
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, show 24 + 4 * 2 = 4 * 8 from rfl,
    show 24 + 4 * 3 = 4 * 9 from rfl, show (24 : Nat) = 4 * 6 from rfl, show 24 + 4 = 4 * 7 from rfl]
  rw [clamp_words4 (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)]
  have a1 := mask1_mod (wv m st (4 * 7))
  have b1 := mask1_mod (wv m st (4 * 8))
  have d1 := mask1_mod (wv m st (4 * 9))
  simp only [rval, r0v, qv, e, Nat.reduceAdd]
  simp only [wv] at a1 b1 d1 ⊢
  omega


theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

/-- The accumulator on entry is less than `p` if the state represents a message. -/
theorem A0_lt {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem ((stp s₀).setWidth 64) key msg) :
    A0 s₀ < P := by
  have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
  rw [← h.2.2] at this
  exact this

/-! ## `blocks` -/

section
variable (s₀ : State)
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
abbrev blR : Region := ⟨(bp s₀).setWidth 64, 16 * nb s₀⟩
/-- The first `i` blocks. -/
abbrev blks (i : Nat) : List Byte := bytesAt s₀.mem ((bp s₀).setWidth 64) (16 * i)
end

structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀, ⟨argAddr s₀ 0, 12⟩]
  wr : s₀.wr = [sR (stp s₀)]
  st_bl : (sR (stp s₀)).Disjoint (blR s₀)
  arg_st : Region.Disjoint ⟨argAddr s₀ 0, 12⟩ (sR (stp s₀))
  ret_st : (retR s₀).Disjoint (sR (stp s₀))
  st_fit : (stp s₀).toNat + 128 ≤ 2 ^ 32
  bl_fit : (bp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 16 ≤ 2 ^ 32

theorem BPre.of (s₀ : State) (h : Proof.Poly1305.blocksX86.pre s₀) : BPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- What holds from `setup` on: the words `F` it left. -/
structure SetupF (s₀ : State) (F : Nat → Nat) : Prop where
  low : ∀ k, k < 18 → k ≠ 5 → F k = words s₀.mem (stp s₀) k
  saved : SavedIn s₀ F
  coefs : Coefs F (r0v s₀.mem (stp s₀)) (qv s₀.mem (stp s₀) 1) (qv s₀.mem (stp s₀) 2)
    (qv s₀.mem (stp s₀) 3)

theorem SetupF.of {s₀ : State} {F : Nat → Nat}
    (hF : ∀ k, (k < 18 ∧ k ≠ 5) ∨ (25 ≤ k ∧ k < 29) → F k = words s₀.mem (stp s₀) k)
    (sv : SavedIn s₀ F) (co : Coefs F (r0v s₀.mem (stp s₀)) (qv s₀.mem (stp s₀) 1) (qv s₀.mem (stp s₀) 2)
      (qv s₀.mem (stp s₀) 3)) : SetupF s₀ F :=
  ⟨fun k h₁ h₂ => hF k (.inl ⟨h₁, h₂⟩), sv, co⟩

/-- The words that absorbing a block and the final reduction store. -/
theorem not_hS {k : Nat} (h : 5 ≤ k ∧ k < 25 ∨ 29 ≤ k) : k ∉ hS := by
  simp only [hS, List.mem_cons, List.not_mem_nil, or_false]; omega

/-- The coefficients, in the words `F` of `setup`, unchanged where the words
outside `hS` are. -/
theorem SetupF.coefs' {s₀ : State} {F : Nat → Nat} (hF : SetupF s₀ F) {g : Nat → Nat}
    (hk : ∀ k < 32, k ∉ hS → g k = F k) :
    Coefs g (r0v s₀.mem (stp s₀)) (qv s₀.mem (stp s₀) 1) (qv s₀.mem (stp s₀) 2) (qv s₀.mem (stp s₀) 3) :=
  hF.coefs.congr fun k h₁ h₂ => hk k (by omega) (not_hS (.inl ⟨by omega, h₂⟩))

/-- The state at the start of block `i` (or after the last), with the words
`F` of `setup`. -/
structure BInv (s₀ : State) (F : Nat → Nat) (i : Nat) (s : State) : Prop where
  ctx : Ctx (stp s₀) s
  esp : s.gpr .esp = s₀.gpr .esp
  esi : s.gpr .esi = bp s₀ + BitVec.ofNat 32 (16 * i)
  frame : Frame [sR (stp s₀)] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ k < 32, k ∉ hS → words s.mem (stp s₀) k = F k
  acc : A0 s₀ < P → words s.mem (stp s₀) 4 ≤ 4 ∧
    hw5 (words s.mem (stp s₀)) % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ i) % P

theorem blocks_eq : blocks = .seq (.block (setup ++ [.mov .esi (.mem (at_ .esp 8)),
    .mov .ecx (.mem (at_ .esp 12)), .alu .test .ecx (.reg .ecx)]))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block (reduce ++ restore))) := rfl

namespace BPre
variable {s₀ : State} (hp : BPre s₀)
include hp

theorem argIn {i : Nat} (hi : i < 3) : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨⟨argAddr s₀ 0, 12⟩, by rw [hp.rd]; simp, arg_contains (n := 12) (by have := hp.sp_fit; omega)
    (by omega)⟩

/-- An argument, in memory the code has written only in the state. -/
theorem arg_same {m : Mem} (hf : Frame [sR (stp s₀)] s₀.mem m) {i : Nat} (hi : i < 3) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (arg_contains (n := 12) (by have := hp.sp_fit; omega) (by omega)) (by simpa using hp.arg_st)
    (by decide)

end BPre

/-- The accumulator on entry, in the words `F` of `setup`. -/
theorem acc_entry {s₀ : State} (hfit : (stp s₀).toNat + 128 ≤ 2 ^ 32) {F : Nat → Nat} (hF : SetupF s₀ F)
    {m : Mem} (hk : ∀ k < 5, words m (stp s₀) k = F k) (hA : A0 s₀ < P) :
    words m (stp s₀) 4 ≤ 4 ∧ hw5 (words m (stp s₀)) % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) [] % P := by
  have hlow : ∀ k, k < 5 → words m (stp s₀) k = words s₀.mem (stp s₀) k := fun k hk' => by
    rw [hk k hk', hF.low k (by omega) (by omega)]
  obtain ⟨-, h4, hv⟩ := acc_words hfit (words_ok s₀.mem _) hA
  refine ⟨by rw [hlow 4 (by omega)]; omega, ?_⟩
  rw [Poly1305.absorbAll_nil]
  simp only [hw5, hlow 0 (by omega), hlow 1 (by omega), hlow 2 (by omega), hlow 3 (by omega),
    hlow 4 (by omega)]
  rw [show A0 s₀ = hw5 (words s₀.mem (stp s₀)) from hv]

theorem prologue_ok {s₀ : State} (hp : BPre s₀) :
    WP isa (.block (setup ++ [.mov .esi (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 12)),
      .alu .test .ecx (.reg .ecx)])) s₀ fun s => ∃ F, SetupF s₀ F ∧
        BInv s₀ F 0 s ∧ s.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  have hfit := hp.st_fit
  refine WP.block_append (WP.mono (setup_ok (arg0_eq s₀) (hp.argIn (i := 0) (by omega)) hfit
    (by rw [hp.wr]; exact List.mem_singleton_self _)) fun s₁ ⟨F, A₁, c₁, hF, sv, co⟩ => ?_)
  have esp₁ := A₁.gpr .esp (by decide)
  have hF' := SetupF.of hF sv co
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 1)) (by rw [ea_at, esp₁])
    (by rw [A₁.rd, A₁.wr]; exact hp.argIn (by omega)) fun s₂ u₂ _ => ?_
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 2)) (by rw [ea_at, u₂.other _ (by decide), esp₁])
    (by rw [u₂.rd, u₂.wr, A₁.rd, A₁.wr]; exact hp.argIn (by omega)) fun s₃ u₃ _ => ?_
  refine wp_test fun s₄ k₄ z₄ => WP.block_nil ⟨F, hF', ?_, ?_⟩
  · have hm : s₄.mem = s₁.mem := by rw [k₄.2.1, u₃.mem, u₂.mem]
    refine ⟨c₁.keep (by rw [k₄.1 _ (by simp), u₃.other _ (by decide), u₂.other _ (by decide)])
      (by rw [k₄.2.2.2, u₃.wr, u₂.wr]), ?_, ?_, ?_, ?_, ?_, fun k hk _ => ?_, fun hA => ?_⟩
    · rw [k₄.1 _ (by simp), u₃.other _ (by decide), u₂.other _ (by decide), esp₁]
    · rw [k₄.1 _ (by simp), u₃.other _ (by decide), u₂.gpr, hp.arg_same A₁.frame (i := 1) (by omega)]
      simp
    · rw [hm]; exact A₁.frame
    · rw [k₄.2.2.1, u₃.rd, u₂.rd, A₁.rd]
    · rw [k₄.2.2.2, u₃.wr, u₂.wr, A₁.wr]
    · rw [hm, words_eq A₁.words hk]
    · exact acc_entry hfit hF' (fun k hk => by rw [hm, words_eq A₁.words (by omega)]) hA
  · rw [z₄, u₃.gpr, u₂.mem, hp.arg_same A₁.frame (i := 2) (by omega)]

theorem blk_addr {bp : BitVec 32} {n i d : Nat} (hfit : bp.toNat + 16 * n ≤ 2 ^ 32) (hi : i < n)
    (hd : d + 4 ≤ 16) :
    addr (bp + BitVec.ofNat 32 (16 * i)) d = bp.setWidth 64 + BitVec.ofNat 64 (16 * i + d) := by
  simp only [addr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := bp.isLt
  rw [Nat.mod_eq_of_lt (a := 16 * i) (by omega), Nat.mod_eq_of_lt (a := bp.toNat + 16 * i) (by omega),
    Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (a := bp.toNat + 16 * i + d) (by omega),
    Nat.mod_eq_of_lt (a := bp.toNat + 16 * i + d) (by omega), Nat.mod_eq_of_lt (a := bp.toNat) (by omega),
    Nat.mod_eq_of_lt (a := 16 * i + d) (by omega), Nat.mod_eq_of_lt (a := bp.toNat + (16 * i + d)) (by omega)]
  omega

theorem blk_contains {bp : BitVec 32} {n i d : Nat} (hfit : bp.toNat + 16 * n ≤ 2 ^ 32) (hi : i < n)
    (hd : d + 4 ≤ 16) {k : Nat} (_hk : 0 < k) (hk' : d + k ≤ 16) :
    (⟨bp.setWidth 64, 16 * n⟩ : Region).Contains (addr (bp + BitVec.ofNat 32 (16 * i)) d) k := by
  rw [blk_addr hfit hi hd]
  simp only [Region.Contains]
  rw [show bp.setWidth 64 + BitVec.ofNat 64 (16 * i + d) - bp.setWidth 64 = BitVec.ofNat 64 (16 * i + d) by
    bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem blk_sub {bp : BitVec 32} {n i d : Nat} (hfit : bp.toNat + 16 * n ≤ 2 ^ 32) (hi : i < n)
    (hd : d + 4 ≤ 16) : Region.Sub (sub (bp + BitVec.ofNat 32 (16 * i)) d 4) ⟨bp.setWidth 64, 16 * n⟩ := by
  intro a ha
  have hc := blk_contains hfit hi hd (k := 4) (by omega) (by omega)
  simp only [Region.Contains] at ha hc ⊢
  have : (a - bp.setWidth 64).toNat ≤ (a - addr (bp + BitVec.ofNat 32 (16 * i)) d).toNat +
      (addr (bp + BitVec.ofNat 32 (16 * i)) d - bp.setWidth 64).toNat := by
    rw [show a - bp.setWidth 64 = (a - addr (bp + BitVec.ofNat 32 (16 * i)) d) +
      (addr (bp + BitVec.ofNat 32 (16 * i)) d - bp.setWidth 64) by bv_omega, BitVec.toNat_add]
    exact Nat.mod_le _ _
  omega

namespace BPre
variable {s₀ : State} (hp : BPre s₀)
include hp

theorem blkIn {s : State} {i : Nat} (hi : i < nb s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hesi : s.gpr .esi = bp s₀ + BitVec.ofNat 32 (16 * i)) : BlkIn s := fun d hd => by
  rw [hrd, hwr, hesi, hp.rd]
  exact ⟨blR s₀, by simp, blk_contains hp.bl_fit hi hd (by omega) (by omega)⟩

theorem blk_disj {i : Nat} (hi : i < nb s₀) {k : Nat} (_hk : k < 4) :
    (sub (bp s₀ + BitVec.ofNat 32 (16 * i)) (4 * k) 4).Disjoint (sR (stp s₀)) :=
  (hp.st_bl.sub_right (blk_sub hp.bl_fit hi (by omega))).symm

/-- The value of block `i`, with the `0x01` byte appended: its four words and `2¹²⁸`. -/
theorem block_value {m : Mem} (hf : Frame [sR (stp s₀)] s₀.mem m) {i : Nat} (hi : i < nb s₀) :
    blkv m (bp s₀ + BitVec.ofNat 32 (16 * i)) 1 =
      leNum (bytesAt s₀.mem ((bp s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) 16 ++ [0x01]) := by
  have hw : ∀ k < 4, wv m (bp s₀ + BitVec.ofNat 32 (16 * i)) (4 * k) =
      w32 s₀.mem ((bp s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) k := fun k hk => by
    show (wd m _ (4 * k)).toNat = _
    rw [wd_frame hf (by simpa using hp.blk_disj hi hk)]
    simp only [wd, w32]
    rw [blk_addr hp.bl_fit hi (by omega), add_ofNat_add]
  rw [Poly1305.leNum_append, Poly1305.length_bytesAt, leNum_bytesAt_16, ← hw 0 (by omega),
    ← hw 1 (by omega), ← hw 2 (by omega), ← hw 3 (by omega)]
  simp only [blkv, Spec.Poly1305.leNum]
  norm_num

end BPre

theorem blks_succ (s₀ : State) (i : Nat) :
    blks s₀ (i + 1) = blks s₀ i ++ bytesAt s₀.mem ((bp s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) 16 := by
  simp only [blks]
  rw [show 16 * (i + 1) = 16 * i + 16 by omega, Poly1305.bytesAt_add]


theorem eval_ne' (s : State) : eval .ne s = s.zf.map (!·) := rfl

theorem body_eq : body = .block (absorb 1 ++ (.alu .add .esi (.imm 16) :: atEnd)) := by
  simp only [body, List.append_assoc, List.singleton_append]

theorem atEnd_eq : atEnd = [.mov .eax (.mem (at_ .esp 12)), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .mov .ecx (.mem (at_ .esp 8)), .alu .add .eax (.reg .ecx), .alu .cmp .eax (.reg .esi)] := rfl

theorem add16_eq (n : BitVec 32) : n + n + (n + n) + (n + n + (n + n)) + (n + n + (n + n) + (n + n + (n + n))) =
    BitVec.ofNat 32 (16 * n.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `16 n + b`, from the arguments `n` at `[esp + 12]` and `b` at `[esp + 8]`,
compared with `esi`. -/
theorem atEnd_ok {s : State} {n b : BitVec 32} (hn : s.mem.readW (addr (s.gpr .esp) 12) 32 = n)
    (hb : s.mem.readW (addr (s.gpr .esp) 8) 32 = b)
    (h12 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4)
    (h8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4) :
    WP isa (.block atEnd) s fun s' => Keeps [.eax, .ecx] s s' ∧
      s'.zf = some (BitVec.ofNat 32 (16 * n.toNat) + b - s.gpr .esi == 0) := by
  rw [atEnd_eq]
  refine wp_movm (a := addr (s.gpr .esp) 12) (ea_at _ _ _) h12 fun s₁ u₁ _ => ?_
  refine wp_addx (readSrc_reg _ _) fun s₂ u₂ _ => wp_addx (readSrc_reg _ _) fun s₃ u₃ _ => ?_
  refine wp_addx (readSrc_reg _ _) fun s₄ u₄ _ => wp_addx (readSrc_reg _ _) fun s₅ u₅ _ => ?_
  have k₅ : Keeps [.eax] s s₅ := ⟨fun r hr => by
      have hr' : r ≠ .eax := by simpa using hr
      rw [u₅.other r hr', u₄.other r hr', u₃.other r hr', u₂.other r hr', u₁.other r hr'],
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  refine wp_movm (a := addr (s.gpr .esp) 8) (by rw [ea_at, k₅.gpr']) (by
    rw [k₅.2.2.1, k₅.2.2.2]; exact h8) fun s₆ u₆ _ => ?_
  refine wp_addx (readSrc_reg _ _) fun s₇ u₇ _ => ?_
  refine wp_cmpx (readSrc_reg _ _) fun s₈ k₈ z₈ _ => WP.block_nil ⟨?_, ?_⟩
  · refine ⟨fun r hr => ?_, by rw [k₈.2.1, u₇.mem, u₆.mem, k₅.2.1], by rw [k₈.2.2.1, u₇.rd, u₆.rd, k₅.2.2.1],
      by rw [k₈.2.2.2, u₇.wr, u₆.wr, k₅.2.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₈.1 r (by simp), u₇.other r hr.1, u₆.other r hr.2, k₅.1 r (by simpa using hr.1)]
  · have e₇ : s₇.gpr .eax = BitVec.ofNat 32 (16 * n.toNat) + b := by
      rw [u₇.gpr, u₆.other _ (by decide), u₆.gpr, k₅.2.1, hb, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hn,
        add16_eq]
    have e₇' : s₇.gpr .esi = s.gpr .esi := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), k₅.gpr' (r := .esi)]
    rw [z₈, e₇, e₇']

theorem end_eq {bp : BitVec 32} {n i : Nat} (hi : i < n) :
    BitVec.ofNat 32 (16 * n) + bp - (bp + BitVec.ofNat 32 (16 * i) + 16) =
      BitVec.ofNat 32 (16 * (n - (i + 1))) := by
  apply BitVec.eq_of_toNat_eq
  have := bp.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [show (16 : BitVec 32).toNat = 16 from rfl]
  omega

theorem ofNat32_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem body_ok {s₀ : State} (hp : BPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {i : Nat}
    (hi : i < nb s₀) {s : State} (hL : BInv s₀ F i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ BInv s₀ F (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ BInv s₀ F (i + 1) s') := by
  have hfit := hp.st_fit
  rw [body_eq]
  refine WP.block_append (WP.mono (absorbFull_ok hL.ctx (hp.blkIn hi hL.rd hL.wr hL.esi)
    (fun k hk => by rw [hL.esi]; exact hp.blk_disj hi hk) 1 (by decide) (C := A0 s₀ < P)
    (fun hA => ⟨hF.coefs' fun k hk hS => hL.keep k hk hS, (hL.acc hA).1⟩)) fun s₁ ⟨S₁, h₁⟩ => ?_)
  have c₁ := hL.ctx.keep (S₁.gpr _ (by decide)) S₁.wr
  refine wp_addx (readSrc_imm _ _) fun s₂ u₂ _ => ?_
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.other _ (by decide), S₁.gpr _ (by decide), hL.esp]
  have hfr₂ : Frame [sR (stp s₀)] s₀.mem s₂.mem := by rw [u₂.mem]; exact hL.frame.trans S₁.frame
  have hrd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, S₁.rd, hL.rd]
  have hwr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, S₁.wr, hL.wr]
  have hesi₂ : s₂.gpr .esi = bp s₀ + BitVec.ofNat 32 (16 * i) + 16 := by
    rw [u₂.gpr, S₁.gpr _ (by decide), hL.esi]
  refine WP.mono (atEnd_ok (n := arg s₀ 2) (b := arg s₀ 1)
    (by rw [esp₂]; exact hp.arg_same hfr₂ (i := 2) (by omega))
    (by rw [esp₂]; exact hp.arg_same hfr₂ (i := 1) (by omega))
    (by rw [hrd₂, hwr₂, esp₂]; exact hp.argIn (i := 2) (by omega))
    (by rw [hrd₂, hwr₂, esp₂]; exact hp.argIn (i := 1) (by omega))) fun s₃ ⟨k₃, z₃⟩ => ?_
  have hm₃ : s₃.mem = s₁.mem := by rw [k₃.2.1, u₂.mem]
  have hc : BInv s₀ F (i + 1) s₃ := by
    refine ⟨c₁.keep (by rw [k₃.gpr', u₂.other _ (by decide)]) (by rw [k₃.2.2.2, u₂.wr]),
      by rw [k₃.gpr']; exact esp₂, ?_, by rw [k₃.2.1]; exact hfr₂, by rw [k₃.2.2.1]; exact hrd₂,
      by rw [k₃.2.2.2]; exact hwr₂, fun k hk hS => ?_, fun hA => ?_⟩
    · rw [k₃.gpr', hesi₂, BitVec.add_assoc, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
        ← BitVec.ofNat_add, show 16 * i + 16 = 16 * (i + 1) by omega]
    · rw [hm₃, show words s₁.mem (stp s₀) k = wv s₁.mem (stp s₀) (4 * k) from rfl, S₁.same k hk hS]
      exact hL.keep k hk hS
    · obtain ⟨h4, hv⟩ := h₁ hA
      obtain ⟨-, hv₀⟩ := hL.acc hA
      refine ⟨by rw [hm₃]; exact h4, ?_⟩
      have h16 : (blks s₀ i).length % 16 = 0 := by simp only [blks, Poly1305.length_bytesAt]; omega
      have hb1 : 0 < (bytesAt s₀.mem ((bp s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) 16).length := by
        rw [Poly1305.length_bytesAt]; omega
      have hb2 : (bytesAt s₀.mem ((bp s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) 16).length ≤ 16 := by
        rw [Poly1305.length_bytesAt]
      rw [hm₃, hv, hL.esi, show (1 : BitVec 32).toNat = 1 from rfl, hp.block_value hL.frame hi,
        mod_step hv₀, blks_succ, Poly1305.absorbAll_append h16, Poly1305.absorbAll_block hb1 hb2]
  have hev : eval .ne s₃ = some (!(decide (16 * (nb s₀ - (i + 1)) = 0))) := by
    rw [eval_ne', z₃, hesi₂, end_eq hi, ofNat32_beq_zero (by have := hp.bl_fit; omega)]
    rfl
  by_cases hlast : i + 1 = nb s₀
  · left
    exact ⟨by rw [hev, ← hlast]; simp, hlast ▸ hc⟩
  · right
    exact ⟨by rw [hev]; simp; omega, by omega, hc⟩

/-! ## Epilogue -/

/-- `h` of a state that represents a message, and its key. -/
theorem repr_acc {s₀ : State} {key msg : List Byte} (hfit : (stp s₀).toNat + 128 ≤ 2 ^ 32)
    (h : Repr s₀.mem ((stp s₀).setWidth 64) key msg) :
    clamp (leNum (key.take 16)) = Rn s₀ ∧ accumulate (Rn s₀) msg = A0 s₀ := by
  have hk : bytesAt s₀.mem ((stp s₀).setWidth 64 + 24) 32 = key := h.2.1
  have hc : clamp (leNum (key.take 16)) = Rn s₀ := by rw [← hk, clamp_key _ hfit]
  exact ⟨hc, by rw [← hc, A0, h.2.2]⟩

/-- What each function leaves in the registers: those `setup` saved. -/
theorem abi_of {s₀ s : State} {F : Nat → Nat} (hsv : SavedIn s₀ F)
    (hb : v s .ebx = F 29) (hs : v s .esi = F 30) (hd : v s .edi = F 31) (hp : v s .ebp = F 5)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hret : s.mem.readW ((s₀.gpr .esp).setWidth 64) 32 =
      s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32) : abiPreserved s₀ s := by
  obtain ⟨b, si, di, bp⟩ := hsv
  refine ⟨fun r hr => ?_, hret⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact BitVec.eq_of_toNat_eq (hb.trans b)
  · exact BitVec.eq_of_toNat_eq (hs.trans si)
  · exact BitVec.eq_of_toNat_eq (hd.trans di)
  · exact BitVec.eq_of_toNat_eq (hp.trans bp)
  · exact hsp

/-- The final reduction and the restoring of the registers: they leave the
reduced `h` and a zero word 5, and the words `hS` do not include is unchanged. -/
theorem finish_ok {st : BitVec 32} {s : State} (hc : Ctx st s) :
    WP isa (.block (reduce ++ restore)) s fun s' =>
      v s' .ebx = words s.mem st 29 ∧ v s' .esi = words s.mem st 30 ∧ v s' .edi = words s.mem st 31 ∧
      v s' .ebp = words s.mem st 5 ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [sR st] s.mem s'.mem ∧ words s'.mem st 5 = 0 ∧
      (∀ k < 32, k ∉ hS → k ≠ 5 → words s'.mem st k = words s.mem st k) ∧
      (words s.mem st 4 ≤ 4 → ∀ k < 5, words s'.mem st k = words s.mem st k ∨ True) ∧
      (words s.mem st 4 ≤ 4 → hw5 (words s'.mem st) = hw5 (words s.mem st) % P) := by
  refine WP.block_append (WP.mono (reduceFull_ok hc) fun s₁ ⟨S₁, h₁⟩ => ?_)
  have c₁ := hc.keep (S₁.gpr _ (by decide)) S₁.wr
  refine WP.mono (restore_ok c₁) fun s₂ ⟨b₂, si₂, di₂, bp₂, sp₂, A₂⟩ => ?_
  have hw : ∀ k < 32, words s₂.mem st k = upd (words s₁.mem st) 5 0 k := fun k hk => A₂.words k hk
  have h1 : ∀ k < 32, k ∉ hS → words s₁.mem st k = words s.mem st k := fun k hk hS =>
    S₁.same k hk hS
  refine ⟨?_, ?_, ?_, ?_, by rw [sp₂, S₁.gpr _ (by decide)], by rw [A₂.rd, S₁.rd], by rw [A₂.wr, S₁.wr],
    S₁.frame.trans A₂.frame, by rw [hw 5 (by omega), upd_same], fun k hk hS h5 => ?_, fun _ _ _ => .inr trivial,
    fun h4 => ?_⟩
  · rw [b₂, h1 29 (by omega) (by decide)]
  · rw [si₂, h1 30 (by omega) (by decide)]
  · rw [di₂, h1 31 (by omega) (by decide)]
  · rw [bp₂, h1 5 (by omega) (by decide)]
  · rw [hw k hk, upd_ne _ _ h5, h1 k hk hS]
  · obtain ⟨hr, -⟩ := h₁ h4
    simp only [hw5, hw 0 (by omega), hw 1 (by omega), hw 2 (by omega), hw 3 (by omega), hw 4 (by omega),
      upd_ne _ _ (show (0 : Nat) ≠ 5 by omega), upd_ne _ _ (show (1 : Nat) ≠ 5 by omega),
      upd_ne _ _ (show (2 : Nat) ≠ 5 by omega), upd_ne _ _ (show (3 : Nat) ≠ 5 by omega),
      upd_ne _ _ (show (4 : Nat) ≠ 5 by omega)]
    exact hr

theorem blocks_epilogue_ok {s₀ : State} (hp : BPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s : State}
    (hL : BInv s₀ F (nb s₀) s) :
    WP isa (.block (reduce ++ restore)) s
      fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.blocksX86.post s₀ s' := by
  have hfit := hp.st_fit
  refine WP.mono (finish_ok hL.ctx) fun s₂ ⟨b₂, si₂, di₂, bp₂, sp₂, _, _, fr₂, z₂, hk₂, _, hr₂⟩ => ?_
  have hframe : Frame [sR (stp s₀)] s₀.mem s₂.mem := hL.frame.trans fr₂
  refine ⟨abi_of hF.saved ?_ ?_ ?_ ?_ (by rw [sp₂, hL.esp]) ?_, fun key msg hrep => ?_⟩
  · rw [b₂, hL.keep 29 (by omega) (by decide)]
  · rw [si₂, hL.keep 30 (by omega) (by decide)]
  · rw [di₂, hL.keep 31 (by omega) (by decide)]
  · rw [bp₂, hL.keep 5 (by omega) (by decide)]
  · exact hframe.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
  · have hA := A0_lt hrep
    obtain ⟨hcl, hac⟩ := repr_acc hfit hrep
    obtain ⟨h4, hv⟩ := hL.acc hA
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; have := hrep.1; omega
    · rw [key_same hfit fun k h₁ h₂ => ?_]
      · exact hrep.2.1
      · rw [hk₂ k (by omega) (not_hS (.inl ⟨by omega, by omega⟩)) (by omega),
          hL.keep k (by omega) (not_hS (.inl ⟨by omega, by omega⟩)), hF.low k (by omega) (by omega)]
    · rw [leNum_acc hfit (words_ok _ _), z₂, hcl, Poly1305.accumulate_append hrep.1, hac, hr₂ h4, hv,
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]
      simp

/-! ## The whole function -/

theorem blocks_correct {s₀ : State} (hp : BPre s₀) :
    WP isa blocks s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.blocksX86.post s₀ s' := by
  rw [blocks_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨F, hF, hL₀, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := BInv s₀ F (nb s₀)) ?_ fun s₂ hc₂ => blocks_epilogue_ok hp hF hc₂)
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hL₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ BInv s₀ F i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ BInv s₀ F (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hF hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩


/-! ## Constant time and satisfiability -/

/-- The taint analysis starts with the stack arguments public, and the word
holding `state` known to be the base address of the writable region. -/
def blocksτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [128], argLen := 16, argBases := [(4, 0)] }

theorem blocks_wf₀ {s : State} (hp : BPre s) : VG.X86.Taint.Wf blocksτ₀ s := by
  have hst := hp.st_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, blocksτ₀], by simp [hp.wr], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_singleton]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega
  · simp only [hp.wr, List.mem_singleton]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 12) (by omega) hp.ret_st hp.arg_st
  · intro p hp'
    simp only [blocksτ₀, List.mem_singleton] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem argMem_eq {s₁ s₂ : State} {n : Nat} (h₁ : (s₁.gpr .esp).toNat + n ≤ 2 ^ 32)
    (h₂ : (s₂.gpr .esp).toNat + n ≤ 2 ^ 32) (ha : ∀ i, 4 + 4 * i < n → arg s₁ i = arg s₂ i) {k : Nat}
    (h4 : 4 ≤ k) (hk : k < n) :
    s₁.mem (VG.X86.Taint.argByte s₁ k) = s₂.mem (VG.X86.Taint.argByte s₂ k) := by
  rw [VG.X86.Taint.argByte_eq h₁ h4 hk, VG.X86.Taint.argByte_eq h₂ h4 hk,
    Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
  exact congrArg _ (ha _ (by omega))

theorem blocks_agree₀ {s₁ s₂ : State} (h₁ : Proof.Poly1305.blocksX86.pre s₁)
    (h₂ : Proof.Poly1305.blocksX86.pre s₂) (hpub : Proof.Poly1305.blocksX86.pub s₁ s₂) :
    VG.X86.Taint.Agree blocksτ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2⟩ := hpub
  have hp₁ := BPre.of _ h₁; have hp₂ := BPre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, blocks_wf₀ hp₁, blocks_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => (Nat.zero_add k).symm ▸ argMem_eq hp₁.sp_fit hp₂.sp_fit (fun i hi => ?_) h4 hk⟩
  · simp only [blocksτ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stp, a0]
  · have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    exacts [a0, a1, a2]

/-- Memory holding the arguments `0x1000, 0x2000, 0` at `0x4004`. -/
def blocksSatMem : Mem := fun a => if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition (with no blocks). -/
def blocksSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := blocksSatMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 12⟩]
  wr := [⟨0x1000, 128⟩]

theorem blocksSat_pre : Proof.Poly1305.blocksX86.pre blocksSat := by
  have a0 : arg blocksSat 0 = 0x1000 := by decide
  have a1 : arg blocksSat 1 = 0x2000 := by decide
  have a2 : arg blocksSat 2 = 0 := by decide
  have e : argAddr blocksSat 0 = 0x4004 := by decide
  simp only [Proof.Poly1305.blocksX86, a0, a1, a2, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, blocksSat] at h₁ h₂
    bv_omega

theorem blocks_verified : Verified X86.target blocks Proof.Poly1305.blocksX86 :=
  ⟨fun s hs => blocks_correct (BPre.of s hs),
    VG.Taint.constantTime (A := taint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
      (by taint_decide),
    ⟨blocksSat, blocksSat_pre⟩⟩

end VG.Proof.Poly1305.X86
