import VerifiedGarbage.Proof.Poly1305.X86.Init

/-!
# Poly1305 on x86 (32-bit): `finalize`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr leBytes mac)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev tp : BitVec 32 := arg s₀ 1
abbrev tl : Nat := (arg s₀ 2).toNat
abbrev op : BitVec 32 := arg s₀ 3
abbrev tR : Region := ⟨(tp s₀).setWidth 64, tl s₀⟩
abbrev oR : Region := ⟨(op s₀).setWidth 64, 16⟩
/-- The message's last bytes. -/
abbrev tail : List Byte := bytesAt s₀.mem ((tp s₀).setWidth 64) (tl s₀)
end

structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [tR s₀, ⟨argAddr s₀ 0, 16⟩]
  wr : s₀.wr = [sR (stp s₀), oR s₀]
  st_t : (sR (stp s₀)).Disjoint (tR s₀)
  st_o : (sR (stp s₀)).Disjoint (oR s₀)
  t_o : (tR s₀).Disjoint (oR s₀)
  arg_st : Region.Disjoint ⟨argAddr s₀ 0, 16⟩ (sR (stp s₀))
  arg_o : Region.Disjoint ⟨argAddr s₀ 0, 16⟩ (oR s₀)
  ret_st : (retR s₀).Disjoint (sR (stp s₀))
  ret_o : (retR s₀).Disjoint (oR s₀)
  st_fit : (stp s₀).toNat + 128 ≤ 2 ^ 32
  t_fit : (tp s₀).toNat + tl s₀ ≤ 2 ^ 32
  o_fit : (op s₀).toNat + 16 ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32
  tl_lt : tl s₀ < 16

theorem FPre.of (s₀ : State) (h : Proof.Poly1305.finalizeX86.pre s₀) : FPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

namespace FPre
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem argIn {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨⟨argAddr s₀ 0, 16⟩, by rw [hp.rd]; simp, arg_contains (n := 16) (by have := hp.sp_fit; omega)
    (by omega)⟩

/-- An argument slot, in memory the code has written only in the state and `out`. -/
theorem arg_same {m : Mem} (hf : Frame [sR (stp s₀), oR s₀] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (arg_contains (n := 16) (by have := hp.sp_fit; omega) (by omega))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl)
        <;> [exact hp.arg_st; exact hp.arg_o]) (by decide)

theorem oIn {d n : Nat} (h : d + n ≤ 16) (hn : 0 < n) : InRegions s₀.wr (addr (op s₀) d) n :=
  ⟨oR s₀, by rw [hp.wr]; simp, by
    have := sub_contains (x := op s₀) (a := 0) (k := 16) (d := d) (n := n) (by have := hp.o_fit; omega)
      (by omega) (by omega) hn
    simpa [sub, addr] using this⟩

end FPre

/-! ## Prologue -/

/-- After the prologue, from the words `F` of `setup`. -/
structure F0 (s₀ : State) (F : Nat → Nat) (s : State) : Prop where
  ctx : Ctx (stp s₀) s
  esp : s.gpr .esp = s₀.gpr .esp
  frame : Frame [sR (stp s₀)] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ k, 6 ≤ k → k < 21 ∨ (25 ≤ k ∧ k < 29) → words s.mem (stp s₀) k = F k
  low : ∀ k, k < 14 → words s.mem (stp s₀) k = words s₀.mem (stp s₀) k

theorem fprologue_ok {s₀ : State} (hp : FPre s₀) :
    WP isa (.block (setup ++ [.mov .ecx (.mem (at_ .esp 12)), .alu .test .ecx (.reg .ecx)])) s₀ fun s =>
      ∃ F, SetupF s₀ F ∧ F0 s₀ F s ∧ s.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  have hfit := hp.st_fit
  refine WP.block_append (WP.mono (setup_ok (arg0_eq s₀) (hp.argIn (i := 0) (by omega)) hfit
    (by rw [hp.wr]; exact List.mem_cons_self)) fun s₁ ⟨F, A₁, c₁, hF, sv, co⟩ => ?_)
  have esp₁ := A₁.gpr .esp (by decide)
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 2)) (by rw [ea_at, esp₁])
    (by rw [A₁.rd, A₁.wr]; exact hp.argIn (by omega)) fun s₂ u₂ _ => wp_test fun s₃ k₃ z₃ => ?_
  have ecx : s₂.gpr .ecx = arg s₀ 2 := by
    rw [u₂.gpr]; exact hp.arg_same (A₁.frame.mono (by simp)) (by omega)
  refine WP.block_nil ⟨F, ⟨fun k hk => hF k (.inl hk), sv, co⟩, ⟨c₁.keep (by rw [k₃.1 _ (by simp),
    u₂.other _ (by decide)]) (by rw [k₃.2.2.2, u₂.wr]), ?_, ?_, ?_, ?_, fun k h₁ h₂ => ?_, fun k hk => ?_⟩, ?_⟩
  · rw [k₃.1 _ (by simp), u₂.other _ (by decide), esp₁]
  · rw [k₃.2.1, u₂.mem]; exact A₁.frame
  · rw [k₃.2.2.1, u₂.rd, A₁.rd]
  · rw [k₃.2.2.2, u₂.wr, A₁.wr]
  · rw [k₃.2.1, u₂.mem, words_eq A₁.words (by omega)]
  · rw [k₃.2.1, u₂.mem, words_eq A₁.words (by omega), hF k (.inl hk)]
  · rw [z₃, ecx]

/-! ## Bytes and regions -/

theorem writeW8_apply (m : Mem) (a x : Addr) (b : Byte) :
    m.writeW a b x = if x = a then b else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have : (x - a).toNat = 0 := by omega
      have : x - a = 0 := BitVec.eq_of_toNat_eq (by simpa using this)
      bv_omega
    simp only [this, h, ite_false]

theorem writeW32_zero_apply (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 32)) x = if (x - a).toNat < 4 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- The bytes `[x + d, x + d + n)` of a region of `k` bytes at `x`. -/
theorem contains0 {x : BitVec 32} {k d n : Nat} (hx : x.toNat + k ≤ 2 ^ 32) (h : d + n ≤ k) (hn : 0 < n) :
    (⟨x.setWidth 64, k⟩ : Region).Contains (addr x d) n := by
  have := sub_contains (x := x) (a := 0) (k := k) (d := d) (n := n) (by omega) (by omega) (by omega) hn
  simpa [sub, addr] using this

theorem sub_sub0 {x : BitVec 32} {k d n : Nat} (hx : x.toNat + k ≤ 2 ^ 32) (h : d + n ≤ k) (hn : 0 < n) :
    Region.Sub (sub x d n) ⟨x.setWidth 64, k⟩ := fun a ha =>
  (contains0 hx h hn).byte (by simp only [Region.Contains] at ha; omega)

theorem addr_zero_add (x : BitVec 32) (j : Nat) : addr (x + BitVec.ofNat 32 j) 0 = addr x j := by
  simp [addr]

theorem addr_inj {x : BitVec 32} {n j k : Nat} (hx : x.toNat + n ≤ 2 ^ 32) (hj : j < n) (hk : k < n)
    (h : addr x j = addr x k) : j = k := by
  have := congrArg BitVec.toNat h
  rw [addr_toNat (by omega), addr_toNat (by omega)] at this
  omega

theorem zero_byte (m : Mem) {x : BitVec 32} (hx : x.toNat + 16 ≤ 2 ^ 32) {d k : Nat} (hd : d + 4 ≤ 16)
    (hk : k < 16) :
    (m.writeW (addr x d) (0 : BitVec 32)) (addr x k) = if d ≤ k ∧ k < d + 4 then 0 else m (addr x k) := by
  rw [writeW32_zero_apply]
  have e : (addr x k - addr x d).toNat < 4 ↔ d ≤ k ∧ k < d + 4 := by
    rw [addr_eq (by omega), addr_eq (by omega)]
    have hb : (x.setWidth 64).toNat < 2 ^ 32 := by rw [BitVec.toNat_setWidth]; have := x.isLt; omega
    generalize x.setWidth 64 = b at *
    constructor <;> intro h <;> bv_omega
  simp only [e]

/-- The words of the state, after writes only to a region disjoint from it. -/
theorem words_frame {m m' : Mem} {st o : BitVec 32} (hst : st.toNat + 128 ≤ 2 ^ 32)
    (hd : (sR st).Disjoint ⟨o.setWidth 64, 16⟩) (hf : Frame [⟨o.setWidth 64, 16⟩] m m') {k : Nat}
    (hk : k < 32) : words m' st k = words m st k := by
  show wv _ _ _ = wv _ _ _
  rw [wv, wv, wd_frame hf (by
    simp only [List.mem_singleton]; rintro r rfl; exact hd.sub_left (sub_sub0 hst (by omega) (by omega)))]

/-! ## After the last bytes -/

/-- After the last bytes (if any) are absorbed. -/
structure TInv (s₀ : State) (F : Nat → Nat) (s : State) : Prop where
  ctx : Ctx (stp s₀) s
  esp : s.gpr .esp = s₀.gpr .esp
  frame : Frame [sR (stp s₀), oR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ k, 6 ≤ k → k < 21 ∨ (25 ≤ k ∧ k < 29) → words s.mem (stp s₀) k = F k
  acc : A0 s₀ < P → words s.mem (stp s₀) 4 ≤ 4 ∧
    hw5 (words s.mem (stp s₀)) % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) % P

theorem tail_nil {s₀ : State} (h : tl s₀ = 0) : tail s₀ = [] := by
  simp [tail, bytesAt, h]

theorem tinv_nil {s₀ : State} (hp : FPre s₀) {F : Nat → Nat} {s : State} (h : F0 s₀ F s) (h0 : tl s₀ = 0) :
    TInv s₀ F s := by
  refine ⟨h.ctx, h.esp, h.frame.mono (by simp), h.rd, h.wr, h.keep, fun hA => ?_⟩
  obtain ⟨-, h4, hv⟩ := acc_words hp.st_fit (words_ok s₀.mem _) hA
  refine ⟨by rw [h.low 4 (by omega)]; omega, ?_⟩
  rw [tail_nil h0, Poly1305.absorbAll_nil]
  simp only [hw5, h.low 0 (by omega), h.low 1 (by omega), h.low 2 (by omega), h.low 3 (by omega),
    h.low 4 (by omega)]
  rw [show A0 s₀ = hw5 (words s₀.mem (stp s₀)) from hv]

/-! ## The last block, copied into `out` -/

/-- Byte `k` of `out` once `j` bytes of the tail are copied. -/
def oByte (s₀ : State) (j k : Nat) : Byte := if k < j then (tail s₀).getD k 0 else 0

/-- The copy loop's invariant, from the state `s₁` after the prologue. -/
structure CpInv (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  ctx : Ctx (stp s₀) s
  esp : s.gpr .esp = s₀.gpr .esp
  ebx : s.gpr .ebx = op s₀ + BitVec.ofNat 32 j
  esi : s.gpr .esi = tp s₀ + BitVec.ofNat 32 j
  ecx : (s.gpr .ecx).toNat = tl s₀ - j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [oR s₀] s₁.mem s.mem
  out : ∀ k < 16, s.mem (addr (op s₀) k) = oByte s₀ j k

theorem zeroOut_ok {s₀ : State} (hp : FPre s₀) {F : Nat → Nat} {s₁ : State} (h₁ : F0 s₀ F s₁) :
    WP isa (.block zeroOut) s₁ (CpInv s₀ s₁ 0) := by
  have ho := hp.o_fit
  have hf₁ : Frame [sR (stp s₀), oR s₀] s₀.mem s₁.mem := h₁.frame.mono (by simp)
  have ino : ∀ d, d + 4 ≤ 16 → InRegions s₁.wr (addr (op s₀) d) 4 := fun d hd => by
    rw [h₁.wr]; exact hp.oIn hd (by omega)
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 3)) (by rw [ea_at, h₁.esp])
    (by rw [h₁.rd, h₁.wr]; exact hp.argIn (by omega)) fun s₂ u₂ _ => ?_
  have ebx : s₂.gpr .ebx = op s₀ := by rw [u₂.gpr]; exact hp.arg_same hf₁ (by omega)
  refine wp_movi fun s₃ u₃ _ => ?_
  have ebx₃ : s₃.gpr .ebx = op s₀ := by rw [u₃.other _ (by decide), ebx]
  refine wp_store (a := addr (op s₀) 0) (by rw [ea_at, ebx₃]) (by rw [u₃.wr, u₂.wr]; exact ino 0 (by omega))
    fun s₄ u₄ => ?_
  refine wp_store (a := addr (op s₀) 4) (by rw [ea_at, u₄.gpr, ebx₃])
    (by rw [u₄.wr, u₃.wr, u₂.wr]; exact ino 4 (by omega)) fun s₅ u₅ => ?_
  refine wp_store (a := addr (op s₀) 8) (by rw [ea_at, u₅.gpr, u₄.gpr, ebx₃])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact ino 8 (by omega)) fun s₆ u₆ => ?_
  refine wp_store (a := addr (op s₀) 12) (by rw [ea_at, u₆.gpr, u₅.gpr, u₄.gpr, ebx₃])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact ino 12 (by omega)) fun s₇ u₇ => ?_
  have esp₇ : s₇.gpr .esp = s₀.gpr .esp := by
    rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h₁.esp]
  have rw₇ : s₇.rd = s₀.rd ∧ s₇.wr = s₀.wr :=
    ⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd],
      by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr]⟩
  have hm : s₇.mem = (((s₁.mem.writeW (addr (op s₀) 0) (0 : BitVec 32)).writeW (addr (op s₀) 4)
      (0 : BitVec 32)).writeW (addr (op s₀) 8) (0 : BitVec 32)).writeW (addr (op s₀) 12) (0 : BitVec 32) := by
    rw [u₇.mem, u₆.gpr, u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.mem, u₂.mem]
  have hf₇ : Frame [oR s₀] s₁.mem s₇.mem := by
    rw [hm]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains0 ho (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains0 ho (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains0 ho (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains0 ho (by omega) (by omega))
  have ha : ∀ i, i < 4 → s₇.mem.readW (addr (s₇.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i := fun i hi => by
    rw [esp₇]; exact hp.arg_same (hf₁.trans (hf₇.mono (by simp))) hi
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 1)) (by rw [ea_at, esp₇])
    (by rw [rw₇.1, rw₇.2]; exact hp.argIn (by omega)) fun s₈ u₈ _ => ?_
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 2)) (by rw [ea_at, u₈.other _ (by decide), esp₇])
    (by rw [u₈.rd, u₈.wr, rw₇.1, rw₇.2]; exact hp.argIn (by omega)) fun s₉ u₉ _ => WP.block_nil ?_
  refine ⟨h₁.ctx.keep ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide)]
  · rw [u₉.wr, u₈.wr, rw₇.2, h₁.wr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), esp₇]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, ebx₃]; simp
  · rw [u₉.other _ (by decide), u₈.gpr, ← esp₇, ha 1 (by omega)]; simp
  · rw [u₉.gpr, u₈.mem, ← esp₇, ha 2 (by omega)]; simp
  · rw [u₉.rd, u₈.rd, rw₇.1]
  · rw [u₉.wr, u₈.wr, rw₇.2]
  · rw [u₉.mem, u₈.mem]; exact hf₇
  · rw [u₉.mem, u₈.mem, hm, zero_byte _ ho (d := 12) (by omega) hk, zero_byte _ ho (d := 8) (by omega) hk,
      zero_byte _ ho (d := 4) (by omega) hk, zero_byte _ ho (d := 0) (by omega) hk]
    simp only [oByte, Nat.not_lt_zero, ite_false]
    split_ifs <;> first | rfl | omega

/-- The copy loop's body. -/
def copyBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .store8 (at_ .ebx 0) .al, .alu .add .esi (.imm 1), .alu .add .ebx (.imm 1),
    .alu .sub .ecx (.imm 1)]

theorem copyLoop_eq : copyLoop = .loop (.block copyBody) .ne := rfl

theorem tail_byte {s₀ : State} (hp : FPre s₀) {j : Nat} (hj : j < tl s₀) :
    (tail s₀).getD j 0 = s₀.mem (addr (tp s₀) j) := by
  rw [addr_eq (by have := hp.t_fit; omega)]
  simp [tail, bytesAt, hj]

theorem add_ofNat_one (x : BitVec 32) (j : Nat) :
    x + BitVec.ofNat 32 j + 1 = x + BitVec.ofNat 32 (j + 1) := by
  rw [BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]

theorem copy_step {s₀ : State} (hp : FPre s₀) {F : Nat → Nat} {s₁ : State} (h₁ : F0 s₀ F s₁) {j : Nat}
    (hj : j < tl s₀) {s : State} (h : CpInv s₀ s₁ j s) :
    WP isa (.block copyBody) s fun s' =>
      CpInv s₀ s₁ (j + 1) s' ∧ s'.zf = some (decide (j + 1 = tl s₀)) := by
  have htl := hp.tl_lt
  have ht := hp.t_fit
  have ho := hp.o_fit
  refine wp_movzx8 (a := addr (tp s₀) j) (by rw [ea_at, h.esi, addr_zero_add])
    (by rw [h.rd, h.wr, hp.rd]; exact ⟨tR s₀, by simp, contains0 ht (by omega) (by omega)⟩) fun s₂ u₂ => ?_
  refine wp_store8 (a := addr (op s₀) j) (by rw [ea_at, u₂.other _ (by decide), h.ebx, addr_zero_add])
    (by rw [u₂.wr, h.wr]; exact hp.oIn (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_addx (readSrc_imm _ _) fun s₄ u₄ _ => wp_addx (readSrc_imm _ _) fun s₅ u₅ _ =>
    wp_subx (readSrc_imm _ _) fun s₆ u₆ z₆ => WP.block_nil ?_
  -- The byte copied is byte `j` of the tail.
  have hbyte : s.mem (addr (tp s₀) j) = (tail s₀).getD j 0 := by
    rw [tail_byte hp hj]
    have hf : Frame [sR (stp s₀), oR s₀] s₀.mem s.mem :=
      (h₁.frame.mono (by simp)).trans (h.frame.mono (by simp))
    have ht' : (tR s₀).Contains (addr (tp s₀) j) 1 := contains0 ht (by omega) (by omega)
    refine hf _ fun r hr hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_t _ hc ht'
    · exact hp.t_o _ ht' hc
  have hmem : s₆.mem = s.mem.writeW (addr (op s₀) j) (s.mem (addr (tp s₀) j)) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, show Reg8.al.reg = .eax from rfl, u₂.gpr, u₂.mem,
      BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
  have ecx : (s.gpr .ecx - 1).toNat = tl s₀ - (j + 1) := by
    rw [BitVec.toNat_sub, h.ecx, show (1 : BitVec 32).toNat = 1 from rfl]; omega
  refine ⟨⟨h.ctx.keep ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide)]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), h.esp]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), h.ebx,
      add_ofNat_one]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), h.esi,
      add_ofNat_one]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), ecx]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr]
  · rw [hmem]; exact h.frame.writeW (List.mem_singleton_self _) _ (contains0 ho (by omega) (by omega))
  · rw [hmem, writeW8_apply]
    by_cases hkj : k = j
    · subst hkj
      rw [ite_eq_left rfl, hbyte, oByte, ite_eq_left (by omega)]
    · rw [ite_eq_right (fun e => hkj (addr_inj ho hk (by omega) e)), h.out k hk, oByte, oByte]
      rcases Nat.lt_or_ge k j with hk' | hk'
      · rw [ite_eq_left hk', ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [z₆, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide)]
    refine congrArg some ?_
    by_cases he : j + 1 = tl s₀
    · rw [decide_eq_true he]
      exact beq_iff_eq.mpr (BitVec.eq_of_toNat_eq (by rw [ecx]; simp; omega))
    · rw [decide_eq_false he]
      exact beq_eq_false_iff_ne.mpr fun h0 => by rw [h0] at ecx; simp at ecx; omega

/-- The padded block: the tail, `0x01`, zeros. -/
def padded (s₀ : State) (k : Nat) : Byte :=
  if k < tl s₀ then (tail s₀).getD k 0 else if k = tl s₀ then 1 else 0

/-- After the `0x01` byte, with `esi` pointing at the padded block in `out`. -/
structure PInv (s₀ s₁ : State) (s : State) : Prop where
  ctx : Ctx (stp s₀) s
  esp : s.gpr .esp = s₀.gpr .esp
  esi : s.gpr .esi = op s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [oR s₀] s₁.mem s.mem
  out : ∀ k < 16, s.mem (addr (op s₀) k) = padded s₀ k

theorem pad_ok {s₀ : State} (hp : FPre s₀) {F : Nat → Nat} {s₁ : State} (h₁ : F0 s₀ F s₁) {s : State}
    (h : CpInv s₀ s₁ (tl s₀) s) :
    WP isa (.block [.mov .eax (.imm 1), .store8 (at_ .ebx 0) .al, .mov .esi (.mem (at_ .esp 16))]) s
      (PInv s₀ s₁) := by
  have htl := hp.tl_lt
  have ho := hp.o_fit
  refine wp_movi fun s₂ u₂ _ => ?_
  refine wp_store8 (a := addr (op s₀) (tl s₀)) (by rw [ea_at, u₂.other _ (by decide), h.ebx, addr_zero_add])
    (by rw [u₂.wr, h.wr]; exact hp.oIn (by omega) (by omega)) fun s₃ u₃ => ?_
  have hmem : s₃.mem = s.mem.writeW (addr (op s₀) (tl s₀)) (1 : Byte) := by
    rw [u₃.mem, show Reg8.al.reg = .eax from rfl, u₂.gpr, u₂.mem]; rfl
  have hf : Frame [oR s₀] s₁.mem s₃.mem := by
    rw [hmem]; exact h.frame.writeW (List.mem_singleton_self _) _ (contains0 ho (by omega) (by omega))
  have esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [u₃.gpr, u₂.other _ (by decide), h.esp]
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 3)) (by rw [ea_at, esp₃])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, h.rd, h.wr]; exact hp.argIn (by omega)) fun s₄ u₄ _ =>
      WP.block_nil ⟨h.ctx.keep ?_ ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide)]
  · rw [u₄.wr, u₃.wr, u₂.wr]
  · rw [u₄.other _ (by decide), esp₃]
  · rw [u₄.gpr]; exact hp.arg_same ((h₁.frame.mono (by simp)).trans (hf.mono (by simp))) (by omega)
  · rw [u₄.rd, u₃.rd, u₂.rd, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, h.wr]
  · rw [u₄.mem]; exact hf
  · rw [u₄.mem, hmem, writeW8_apply]
    by_cases hkj : k = tl s₀
    · subst hkj
      rw [ite_eq_left rfl, padded, ite_eq_right (by omega), ite_eq_left rfl]
    · rw [ite_eq_right (fun e => hkj (addr_inj ho hk (by omega) e)), h.out k hk, oByte, padded]
      rcases Nat.lt_or_ge k (tl s₀) with hk' | hk'
      · rw [ite_eq_left hk', ite_eq_left hk']
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hkj]

/-- The padded block as a number: the tail with `0x01` appended. -/
theorem padded_value {s₀ : State} (hp : FPre s₀) {m : Mem}
    (h : ∀ k < 16, m (addr (op s₀) k) = padded s₀ k) :
    blkv m (op s₀) (0 : BitVec 32).toNat = leNum (tail s₀ ++ [0x01]) := by
  have htl := hp.tl_lt
  have ho := hp.o_fit
  have hl : (List.range 16).map (padded s₀) = (tail s₀ ++ [0x01]) ++ List.replicate (15 - tl s₀) 0 := by
    apply List.ext_getElem
    · simp [tail, Poly1305.length_bytesAt]; omega
    · intro k h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      have hlen : (tail s₀).length = tl s₀ := Poly1305.length_bytesAt _ _ _
      rcases Nat.lt_trichotomy k (tl s₀) with hk | rfl | hk
      · rw [List.getElem_append_left (by simp [hlen]; omega), List.getElem_append_left (by omega)]
        simp only [padded, hk, ite_true]
        simp [tail, bytesAt, hk]
      · rw [List.getElem_append_left (by simp [hlen]), List.getElem_append_right (by omega)]
        simp [padded, hlen]
      · rw [List.getElem_append_right (by simp [hlen]; omega)]
        simp [padded, show ¬ k < tl s₀ by omega, show k ≠ tl s₀ by omega]
  have hb : bytesAt m ((op s₀).setWidth 64) 16 = (List.range 16).map (padded s₀) := by
    simp only [bytesAt]
    apply List.map_congr_left
    intro k hk
    have hk := List.mem_range.mp hk
    rw [← h k hk, addr_eq (by omega)]
  have e : ∀ k < 4, w32 m ((op s₀).setWidth 64) k = wv m (op s₀) (4 * k) := fun k hk => by
    simp only [w32, wv, wd]; rw [addr_eq (by omega)]
  have hv := leNum_bytesAt_16 m ((op s₀).setWidth 64)
  rw [hb, hl, Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero, Nat.mul_zero,
    Nat.add_zero, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)] at hv
  rw [hv]
  rfl

theorem lastBlock_ok {s₀ : State} (hp : FPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s₁ : State}
    (h₁ : F0 s₀ F s₁) (hpos : 0 < tl s₀) : WP isa lastBlock s₁ (TInv s₀ F) := by
  have htl := hp.tl_lt
  have hfit := hp.st_fit
  refine WP.seq (WP.mono (zeroOut_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (Q := CpInv s₀ s₁ (tl s₀)) ?_ fun s₃ h₃ => ?_)
  · -- The copy loop.
    rw [copyLoop_eq]
    let Inv : Nat → State → Prop := fun n s => ∃ j, n = tl s₀ - j ∧ j < tl s₀ ∧ CpInv s₀ s₁ j s
    have hstep : ∀ n s, Inv n s → WP isa (.block copyBody) s (fun s' =>
        (eval .ne s' = some false ∧ CpInv s₀ s₁ (tl s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨j, rfl, hj, h⟩
      refine WP.mono (copy_step hp h₁ hj h) fun s' ⟨h', hz⟩ => ?_
      by_cases hl : j + 1 = tl s₀
      · exact .inl ⟨by simp [eval, hz, hl], hl ▸ h'⟩
      · exact .inr ⟨by simp [eval, hz, hl], tl s₀ - (j + 1), by omega, j + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep (tl s₀) s₂ ⟨0, by simp, hpos, h₂⟩
  · -- The `0x01` byte, and the block.
    refine WP.block_append (WP.mono (pad_ok hp h₁ h₃) fun s₄ h₄ => ?_)
    have hw₄ : ∀ k < 32, words s₄.mem (stp s₀) k = words s₁.mem (stp s₀) k := fun k hk =>
      words_frame hfit hp.st_o h₄.frame hk
    have hco : Coefs (words s₄.mem (stp s₀)) (r0v s₀.mem (stp s₀)) (qv s₀.mem (stp s₀) 1)
        (qv s₀.mem (stp s₀) 2) (qv s₀.mem (stp s₀) 3) :=
      hF.coefs.congr fun k h₁' h₂' => by rw [hw₄ k (by omega)]; exact h₁.keep k (by omega) (.inl h₂')
    have hb : BlkIn s₄ := fun d hd => by
      rw [h₄.rd, h₄.wr, h₄.esi]
      exact ⟨oR s₀, by rw [hp.wr]; simp, contains0 hp.o_fit (by omega) (by omega)⟩
    have hd : ∀ k < 4, (sub (s₄.gpr .esi) (4 * k) 4).Disjoint (sR (stp s₀)) := fun k hk => by
      rw [h₄.esi]; exact (hp.st_o.sub_right (sub_sub0 hp.o_fit (by omega) (by omega))).symm
    have hv₄ : A0 s₀ < P → words s₄.mem (stp s₀) 4 ≤ 4 ∧ hw5 (words s₄.mem (stp s₀)) = A0 s₀ := fun hA => by
      obtain ⟨-, h4, hv⟩ := acc_words hfit (words_ok s₀.mem _) hA
      refine ⟨by rw [hw₄ 4 (by omega), h₁.low 4 (by omega)]; omega, ?_⟩
      simp only [hw5, hw₄ 0 (by omega), hw₄ 1 (by omega), hw₄ 2 (by omega), hw₄ 3 (by omega),
        hw₄ 4 (by omega), h₁.low 0 (by omega), h₁.low 1 (by omega), h₁.low 2 (by omega),
        h₁.low 3 (by omega), h₁.low 4 (by omega)]
      exact hv.symm
    refine WP.mono (absorbFull_ok h₄.ctx hb hd 0 (by decide) (C := A0 s₀ < P)
      fun hA => ⟨hco, (hv₄ hA).1⟩) fun s₅ ⟨S₅, h₅⟩ => ?_
    refine ⟨h₄.ctx.keep (S₅.gpr _ (by decide)) S₅.wr, by rw [S₅.gpr _ (by decide), h₄.esp], ?_,
      by rw [S₅.rd, h₄.rd], by rw [S₅.wr, h₄.wr], fun k h₁' h₂' => ?_, fun hA => ?_⟩
    · exact (h₁.frame.mono (by simp)).trans ((h₄.frame.mono (by simp)).trans (S₅.frame.mono (by simp)))
    · have hk : k < 32 := by omega
      rw [show words s₅.mem (stp s₀) k = wv s₅.mem (stp s₀) (4 * k) from rfl, S₅.same k hk (by simp; omega)]
      exact (hw₄ k hk).trans (h₁.keep k h₁' h₂')
    · obtain ⟨h4, hv⟩ := h₅ hA
      refine ⟨h4, ?_⟩
      have hlen : (tail s₀).length = tl s₀ := Poly1305.length_bytesAt _ _ _
      rw [hv, (hv₄ hA).2, h₄.esi, padded_value hp h₄.out, Poly1305.absorbAll_block (by omega) (by omega),
        Nat.mod_mod, Nat.mul_comm]

/-! ## The tag -/

theorem words_lt (m : Mem) (st : BitVec 32) (k : Nat) : words m st k < 2 ^ 32 := BitVec.isLt _

/-- Word `i` of `h` plus word `i` of `s`. -/
abbrev ta (m : Mem) (st : BitVec 32) (i : Nat) : Nat := words m st i + words m st (10 + i)

/-- The carry into word `k` of the tag. -/
def cs (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (a k + cs a k) / 2 ^ 32

theorem cs_succ (a : Nat → Nat) (k : Nat) : cs a (k + 1) = (a k + cs a k) / 2 ^ 32 := rfl

theorem cs_le {a : Nat → Nat} (ha : ∀ i, a i < 2 ^ 33 - 1) : ∀ k, cs a k ≤ 1
  | 0 => Nat.zero_le _
  | k + 1 => by rw [cs_succ]; have := cs_le ha k; have := ha k; omega

/-- The words of the tag: those of `x + y` modulo `2¹²⁸`. -/
theorem tag_words (x y : Nat → Nat) {X : Nat}
    (hX : X % 2 ^ 128 = x 0 + 2 ^ 32 * x 1 + 2 ^ 64 * x 2 + 2 ^ 96 * x 3) {k : Nat} (hk : k < 4) :
    (x k + y k + cs (fun i => x i + y i) k) % 2 ^ 32 =
      (X + (y 0 + 2 ^ 32 * y 1 + 2 ^ 64 * y 2 + 2 ^ 96 * y 3)) / 2 ^ (32 * k) % 2 ^ 32 := by
  obtain ⟨a0, a1, a2, a3⟩ := addS_arith (x0 := x 0) (x1 := x 1) (x2 := x 2) (x3 := x 3) (s0 := y 0)
    (s1 := y 1) (s2 := y 2) (s3 := y 3) X _ hX rfl
  have c1 : cs (fun i => x i + y i) 1 = (x 0 + y 0) / 2 ^ 32 := rfl
  have c2 : cs (fun i => x i + y i) 2 = (x 1 + y 1 + (x 0 + y 0) / 2 ^ 32) / 2 ^ 32 := rfl
  have c3 : cs (fun i => x i + y i) 3 =
      (x 2 + y 2 + (x 1 + y 1 + (x 0 + y 0) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32 := rfl
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [show cs (fun i => x i + y i) 0 = 0 from rfl, Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    exact a0
  · rw [c1]; exact a1
  · rw [c2]; exact a2
  · rw [c3]; exact a3

/-- The tag's words so far, from the state `s` before them. -/
structure TagInv (st o : BitVec 32) (s : State) (k : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨o.setWidth 64, 16⟩] s.mem s'.mem
  out : ∀ i < k, wv s'.mem o (4 * i) = (ta s.mem st i + cs (ta s.mem st) i) % 2 ^ 32
  cf : 0 < k → ∃ c, s'.cf = some c ∧ c.toNat = cs (ta s.mem st) k

theorem tagWord_ok {st o : BitVec 32} {s₁ : State} (hc : Ctx st s₁) (ho : o.toNat + 16 ≤ 2 ^ 32)
    (hesi : s₁.gpr .esi = o) (hout : (⟨o.setWidth 64, 16⟩ : Region) ∈ s₁.wr)
    (hd : (sR st).Disjoint ⟨o.setWidth 64, 16⟩) {k : Nat} (hk : k < 4) {s : State}
    (h : TagInv st o s₁ k s) :
    WP isa (.block [.mov .eax (.mem (at_ .edi (hOff k))),
      .alu (if k = 0 then .add else .adc) .eax (.mem (at_ .edi (40 + 4 * k))),
      .store (at_ .esi (4 * k)) .eax]) s (TagInv st o s₁ (k + 1)) := by
  have hfit := hc.fit
  have hw : ∀ j < 32, words s.mem st j = words s₁.mem st j := fun j hj => words_frame hfit hd h.frame hj
  have edi : s.gpr .edi = st := by rw [h.gpr _ (by decide), hc.edi]
  have hta : ∀ i, ta s₁.mem st i < 2 ^ 33 - 1 := fun i => by
    have := words_lt s₁.mem st i; have := words_lt s₁.mem st (10 + i)
    show words s₁.mem st i + words s₁.mem st (10 + i) < _
    omega
  have hcs : cs (ta s₁.mem st) k ≤ 1 := cs_le hta k
  have htk := hta k
  refine wp_movm (a := addr st (4 * k)) (by rw [ea_at, edi]; rfl)
    (by rw [h.rd, h.wr]; exact hc.inRW (by omega) (by omega)) fun s₂ u₂ cf₂ => ?_
  have e₂ : (s₂.gpr .eax).toNat = words s₁.mem st k := by rw [u₂.gpr, ← hw k (by omega)]; rfl
  have hx : readSrc s₂ (.mem (at_ .edi (40 + 4 * k))) = some (s.mem.readW (addr st (40 + 4 * k)) 32) := by
    rw [readSrc_mem (a := addr st (40 + 4 * k)) (by rw [ea_at, u₂.other _ (by decide), edi])
      (by rw [u₂.rd, u₂.wr, h.rd, h.wr]; exact hc.inRW (by omega) (by omega)), u₂.mem]
  have ex : (s.mem.readW (addr st (40 + 4 * k)) 32).toNat = words s₁.mem st (10 + k) := by
    rw [← hw (10 + k) (by omega)]
    show _ = wv _ _ (4 * (10 + k))
    rw [show 4 * (10 + k) = 40 + 4 * k by omega]
  have fin : ∀ (s₃ : State) (y : BitVec 32), Upd s₂ s₃ .eax y →
      y.toNat = (ta s₁.mem st k + cs (ta s₁.mem st) k) % 2 ^ 32 →
      s₃.cf = some (decide (2 ^ 32 ≤ ta s₁.mem st k + cs (ta s₁.mem st) k)) →
      WP isa (.block [.store (at_ .esi (4 * k)) .eax]) s₃ (TagInv st o s₁ (k + 1)) := by
    intro s₃ y u₃ hy cf₃
    refine wp_store (a := addr o (4 * k))
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), h.gpr _ (by decide), hesi])
      (by rw [u₃.wr, u₂.wr, h.wr]; exact ⟨_, hout, contains0 ho (by omega) (by omega)⟩) fun s₄ u₄ =>
        WP.block_nil ⟨fun r hr => ?_, ?_, ?_, ?_, fun i hi => ?_, fun _ => ⟨_, by rw [u₄.cf]; exact cf₃, ?_⟩⟩
    · rw [u₄.gpr, u₃.other r hr, u₂.other r hr, h.gpr r hr]
    · rw [u₄.rd, u₃.rd, u₂.rd, h.rd]
    · rw [u₄.wr, u₃.wr, u₂.wr, h.wr]
    · rw [u₄.mem, u₃.mem, u₂.mem]
      exact h.frame.writeW (List.mem_singleton_self _) _ (contains0 ho (by omega) (by omega))
    · rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem]
      by_cases hik : i = k
      · subst hik; rw [wv, wd_write_self]; exact hy
      · rw [wv, wd_write_ne _ _ (by omega) (by omega) (by omega)]; exact h.out i (by omega)
    · rw [carry_dec (by omega), cs_succ]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [ite_eq_left rfl]
    refine wp_addx hx fun s₃ u₃ cf₃ => fin s₃ _ u₃ ?_ ?_
    · rw [BitVec.toNat_add, e₂, ex]; rfl
    · rw [cf₃, e₂, ex]; rfl
  · rw [ite_eq_right (by omega)]
    obtain ⟨c, hcf, hcv⟩ := h.cf hk0
    refine wp_adcx hx (by rw [cf₂, hcf]) fun s₃ u₃ cf₃ => fin s₃ _ u₃ ?_ ?_
    · rw [add3_toNat, e₂, ex, hcv]
    · rw [cf₃, e₂, ex, hcv]

/-- `addS`: the tag into `out`. -/
theorem addS_ok {st o : BitVec 32} {s : State} (hc : Ctx st s) (ho : o.toNat + 16 ≤ 2 ^ 32)
    (harg : s.mem.readW (addr (s.gpr .esp) 16) 32 = o)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4)
    (hout : (⟨o.setWidth 64, 16⟩ : Region) ∈ s.wr) (hd : (sR st).Disjoint ⟨o.setWidth 64, 16⟩) :
    WP isa (.block addS) s fun s' => (∀ r, r ≠ .eax → r ≠ .esi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Frame [⟨o.setWidth 64, 16⟩] s.mem s'.mem ∧
      ∀ i < 4, wv s'.mem o (4 * i) = (ta s.mem st i + cs (ta s.mem st) i) % 2 ^ 32 := by
  refine wp_movm (a := addr (s.gpr .esp) 16) (ea_at _ _ _) hin fun s₁ u₁ _ => ?_
  have c₁ : Ctx st s₁ := hc.keep (u₁.other _ (by decide)) u₁.wr
  have esi : s₁.gpr .esi = o := by rw [u₁.gpr, harg]
  have ind : ∀ n ≤ 4, WP isa (.block ((List.range n).flatMap fun k => [.mov .eax (.mem (at_ .edi (hOff k))),
      .alu (if k = 0 then .add else .adc) .eax (.mem (at_ .edi (40 + 4 * k))),
      .store (at_ .esi (4 * k)) .eax])) s₁ (TagInv st o s₁ n) := by
    intro n hn
    induction n with
    | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega),
        fun h => absurd h (by omega)⟩
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact WP.block_append (WP.mono (ih (by omega)) fun s' h' =>
        tagWord_ok c₁ ho esi (by rw [u₁.wr]; exact hout) hd (by omega) h')
  refine WP.mono (ind 4 le_rfl) fun s₂ h₂ =>
    ⟨fun r h₁ h₂' => ?_, by rw [h₂.rd, u₁.rd], by rw [h₂.wr, u₁.wr], ?_, fun i hi => ?_⟩
  · rw [h₂.gpr r h₁, u₁.other r h₂']
  · rw [← u₁.mem]; exact h₂.frame
  · rw [h₂.out i hi, u₁.mem]

/-! ## Epilogue -/

theorem fepilogue_ok {s₀ : State} (hp : FPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s : State}
    (hL : TInv s₀ F s) :
    WP isa (.block (reduce ++ addS ++ restore)) s
      fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.finalizeX86.post s₀ s' := by
  have hfit := hp.st_fit
  have ho := hp.o_fit
  refine WP.block_append (WP.block_append (WP.mono (reduceFull_ok hL.ctx) fun s₁ ⟨S₁, h₁⟩ => ?_))
  have c₁ := hL.ctx.keep (S₁.gpr _ (by decide)) S₁.wr
  have esp₁ : s₁.gpr .esp = s₀.gpr .esp := by rw [S₁.gpr _ (by decide), hL.esp]
  have hf₁ : Frame [sR (stp s₀), oR s₀] s₀.mem s₁.mem := hL.frame.trans (S₁.frame.mono (by simp))
  refine WP.mono (addS_ok c₁ ho (by rw [esp₁]; exact hp.arg_same hf₁ (i := 3) (by omega))
    (by rw [S₁.rd, S₁.wr, hL.rd, hL.wr, esp₁]; exact hp.argIn (i := 3) (by omega))
    (by rw [S₁.wr, hL.wr, hp.wr]; simp) hp.st_o) fun s₂ ⟨g₂, rd₂, wr₂, f₂, o₂⟩ => ?_
  have c₂ : Ctx (stp s₀) s₂ := c₁.keep (g₂ _ (by decide) (by decide)) wr₂
  refine WP.mono (restore_ok c₂) fun s₃ ⟨b₃, si₃, di₃, bp₃, sp₃, m₃⟩ => ?_
  -- Words of the state that neither the reduction nor the tag changes.
  have hk : ∀ k < 32, k ∉ hS → words s₃.mem (stp s₀) k = words s.mem (stp s₀) k := by
    intro k hk h₁'
    rw [m₃, words_frame hfit hp.st_o f₂ hk]
    exact S₁.same k hk h₁'
  have hframe : Frame [sR (stp s₀), oR s₀] s₀.mem s₃.mem := by
    rw [m₃]; exact hf₁.trans (f₂.mono (by simp))
  refine ⟨abi_of hF.saved ?_ ?_ ?_ ?_ ?_ ?_, fun key msg hrep => ?_⟩
  · rw [b₃, show words s₂.mem (stp s₀) 25 = words s₃.mem (stp s₀) 25 by rw [m₃],
      hk 25 (by omega) (by decide), hL.keep 25 (by omega) (.inr ⟨by omega, by omega⟩)]
  · rw [si₃, show words s₂.mem (stp s₀) 26 = words s₃.mem (stp s₀) 26 by rw [m₃],
      hk 26 (by omega) (by decide), hL.keep 26 (by omega) (.inr ⟨by omega, by omega⟩)]
  · rw [di₃, show words s₂.mem (stp s₀) 27 = words s₃.mem (stp s₀) 27 by rw [m₃],
      hk 27 (by omega) (by decide), hL.keep 27 (by omega) (.inr ⟨by omega, by omega⟩)]
  · rw [bp₃, show words s₂.mem (stp s₀) 28 = words s₃.mem (stp s₀) 28 by rw [m₃],
      hk 28 (by omega) (by decide), hL.keep 28 (by omega) (.inr ⟨by omega, by omega⟩)]
  · rw [sp₃, g₂ _ (by decide) (by decide), esp₁]
  · refine hframe.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hp.ret_st, hp.ret_o]
  · have hA := A0_lt hrep
    obtain ⟨hcl, hac⟩ := repr_acc hfit hrep
    obtain ⟨h4, hv⟩ := hL.acc hA
    obtain ⟨hr, -⟩ := h₁ h4
    -- `h`, reduced.
    have hX : hw5 (words s₁.mem (stp s₀)) = accumulate (clamp (leNum (key.take 16))) (msg ++ tail s₀) := by
      rw [hr, hv, hcl, Poly1305.accumulate_append hrep.1, hac, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]
    -- `s`, words 10 to 13 of the state.
    have e : ∀ k < 4, words s₁.mem (stp s₀) (10 + k) = wv s₀.mem (stp s₀) (24 + 16 + 4 * k) := by
      intro k hk
      rw [show words s₁.mem (stp s₀) (10 + k) = wv s₁.mem (stp s₀) (4 * (10 + k)) from rfl,
        S₁.same _ (by omega) (by simp; omega)]
      have := (hL.keep (10 + k) (by omega) (.inl (by omega))).trans (hF.low (10 + k) (by omega))
      simp only [words] at this
      rw [this, show 4 * (10 + k) = 24 + 16 + 4 * k by omega]
    have hSk : leNum ((key.drop 16).take 16) = words s₁.mem (stp s₀) (10 + 0) +
        2 ^ 32 * words s₁.mem (stp s₀) (10 + 1) + 2 ^ 64 * words s₁.mem (stp s₀) (10 + 2) +
        2 ^ 96 * words s₁.mem (stp s₀) (10 + 3) := by
      rw [← hrep.2.1, show bytesAt s₀.mem ((stp s₀).setWidth 64 + 24) 32 =
          bytesAt s₀.mem ((stp s₀).setWidth 64 + 24) (16 + 16) from rfl, Poly1305.bytesAt_add,
        List.drop_left' (Poly1305.length_bytesAt _ _ _),
        List.take_of_length_le (by rw [Poly1305.length_bytesAt]), leNum_bytesAt_16,
        show (24 : Addr) = BitVec.ofNat 64 24 from rfl, add_ofNat_add, w32_off hfit (by omega),
        w32_off hfit (by omega), w32_off hfit (by omega), w32_off hfit (by omega), e 0 (by omega),
        e 1 (by omega), e 2 (by omega), e 3 (by omega)]
    have hXm : hw5 (words s₁.mem (stp s₀)) % 2 ^ 128 = words s₁.mem (stp s₀) 0 +
        2 ^ 32 * words s₁.mem (stp s₀) 1 + 2 ^ 64 * words s₁.mem (stp s₀) 2 +
        2 ^ 96 * words s₁.mem (stp s₀) 3 := by
      have := words_lt s₁.mem (stp s₀) 0; have := words_lt s₁.mem (stp s₀) 1
      have := words_lt s₁.mem (stp s₀) 2; have := words_lt s₁.mem (stp s₀) 3
      simp only [hw5, val5]
      omega
    rw [m₃]
    show bytesAt s₂.mem ((op s₀).setWidth 64) 16 = leBytes 16
      (accumulate (clamp (leNum (key.take 16))) (msg ++ tail s₀) + leNum ((key.drop 16).take 16))
    rw [← hX, hSk]
    refine bytesAt_leBytes_16w _ _ _ fun k hk => ?_
    rw [show w32 s₂.mem ((op s₀).setWidth 64) k = wv s₂.mem (op s₀) (4 * k) by
      simp only [w32, wv, wd]; rw [addr_eq (by omega)], o₂ k hk]
    exact tag_words (fun i => words s₁.mem (stp s₀) i) (fun i => words s₁.mem (stp s₀) (10 + i)) hXm hk

/-! ## The whole function -/

theorem finalize_correct {s₀ : State} (hp : FPre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.finalizeX86.post s₀ s' := by
  refine WP.seq (WP.mono (fprologue_ok hp) fun s₁ ⟨F, hF, h₁, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := TInv s₀ F) ?_ fun s₂ h₂ => fepilogue_ok hp hF h₂)
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : tl s₀ = 0 := by simp at h; simp [tl, h]
    exact WP.block_nil (M := isa) (tinv_nil hp h₁ h0)
  · have hpos : 0 < tl s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    exact lastBlock_ok hp hF h₁ hpos

/-! ## Constant time and satisfiability -/

/-- The taint analysis starts with the stack arguments public, and the words
holding `state` and `out` known to be the bases of the writable regions. -/
def finalizeτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [128, 16], argLen := 20,
    argBases := [(4, 0), (16, 1)] }

theorem finalize_wf₀ {s : State} (hp : FPre s) : VG.X86.Taint.Wf finalizeτ₀ s := by
  have hst := hp.st_fit; have ho := hp.o_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, finalizeτ₀], by simpa [hp.wr] using hp.st_o, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_o hp.arg_o
  · intro p hp'
    simp only [finalizeτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by decide, ?_⟩
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
    · refine ⟨by decide, ?_⟩
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem finalize_agree₀ {s₁ s₂ : State} (h₁ : Proof.Poly1305.finalizeX86.pre s₁)
    (h₂ : Proof.Poly1305.finalizeX86.pre s₂) (hpub : Proof.Poly1305.finalizeX86.pub s₁ s₂) :
    VG.X86.Taint.Agree finalizeτ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := FPre.of _ h₁; have hp₂ := FPre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, finalize_wf₀ hp₁, finalize_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => (Nat.zero_add k).symm ▸ argMem_eq hp₁.sp_fit hp₂.sp_fit (fun i hi => ?_) h4 hk⟩
  · simp only [finalizeτ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stp, oR, op, a0, a3]
  · have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by change 4 + 4 * i < 20 at hi; omega
    rcases this with rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3]

/-- Memory holding the arguments `0x1000, 0x2000, 0, 0x3000` at `0x4004`. -/
def finalizeSatMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x4011 then 0x30 else 0

/-- A state satisfying the precondition (with no tail). -/
def finalizeSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := finalizeSatMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x3000, 16⟩]

theorem finalizeSat_pre : Proof.Poly1305.finalizeX86.pre finalizeSat := by
  have a0 : arg finalizeSat 0 = 0x1000 := by decide
  have a1 : arg finalizeSat 1 = 0x2000 := by decide
  have a2 : arg finalizeSat 2 = 0 := by decide
  have a3 : arg finalizeSat 3 = 0x3000 := by decide
  have e : argAddr finalizeSat 0 = 0x4004 := by decide
  simp only [Proof.Poly1305.finalizeX86, a0, a1, a2, a3, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, finalizeSat] at h₁ h₂
    bv_omega

theorem finalize_verified : Verified X86.target finalize Proof.Poly1305.finalizeX86 :=
  ⟨fun s hs => finalize_correct (FPre.of s hs),
    VG.Taint.constantTime (A := taint) finalizeτ₀ (fun _ _ h₁ h₂ hp => finalize_agree₀ h₁ h₂ hp)
      (by taint_decide),
    ⟨finalizeSat, finalizeSat_pre⟩⟩

end VG.Proof.Poly1305.X86
