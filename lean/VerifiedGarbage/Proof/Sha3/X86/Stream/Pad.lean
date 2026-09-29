import VerifiedGarbage.Proof.Sha3.X86.Permute
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The SHA-3 sponge on x86 (32-bit): `pad`

Untrusted: everything here is checked by Lean. The structure of the x86-64
proof (`VG.Proof.Sha3.X86_64.Stream.Pad`): two bytes of the state XORed,
then the permutation, with `ebx` and `esi` saved in the scratch space.
-/

namespace VG.Proof.Sha3.X86.Stream.Pad

open VG VG.X86 VG.Impl.Sha3.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movm wp_movzx8 wp_store wp_store8 wp_add wp_subi
  contains_addr addr_toNat)
open VG.Proof.Sha3.X86 (permuteCall_ok reg32 wp_xorm)
open VG.Proof.Sha3 (Rep xorByte stateAt_xorByte absorb_pad writeW8_apply ne_of_lt200 rate_bounds
  contains_offset)
open VG.Spec.Sha3 (stateAt keccakF rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev rt : Nat := (arg s₀ 1).toNat
abbrev pos : Nat := (arg s₀ 2).toNat
abbrev scr : BitVec 32 := arg s₀ 4
abbrev stA : Addr := (st s₀).setWidth 64
abbrev stR : Region := ⟨stA s₀, 200⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 640⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 12

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scR s₀, argR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + 200 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 640 ≤ 2 ^ 32
  sp_lo : 12 ≤ (E s₀).toNat
  sp_fit : (E s₀).toNat + 24 ≤ 2 ^ 32
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.padX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  have e := stk_eq h12
  exact ⟨h1, h2, h3, h4, h5, h6, h7, by show (below _ _).Disjoint _; rw [e]; exact h8,
    by show (below _ _).Disjoint _; rw [e]; exact h9, h10, h11, h12, h13, h14, h15⟩

theorem argR_eq (s₀ : State) : argR s₀ = ⟨addr (E s₀) 4, 20⟩ := rfl

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem rt_pos : 72 ≤ rt s₀ ∧ rt s₀ ≤ 168 := rate_bounds hp.rate

theorem arg_in {s : State} (hw : s.wr = s₀.wr) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 24) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) d) 4 :=
  ⟨argR s₀, by simp [hw, hp.wr], by rw [argR_eq s₀]; exact arg_contains (by have := hp.sp_fit; omega) h₁ h₂⟩

/-- The argument words are never written. -/
theorem arg_keep {m : Mem} (hf : Frame [stR s₀, scR s₀] s₀.mem m) {d : Nat} (h₁ : 4 ≤ d)
    (h₂ : d + 4 ≤ 24) : m.readW (addr (E s₀) d) 32 = s₀.mem.readW (addr (E s₀) d) 32 := by
  have fit : (E s₀).toNat + 4 + 20 ≤ 2 ^ 32 := by have := hp.sp_fit; omega
  have hs := arg_word fit h₁ h₂
  refine hf.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (argR_eq s₀ ▸ hp.a_st).sub_left hs
  · exact (argR_eq s₀ ▸ hp.a_scr).sub_left hs

theorem scr_out {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 640) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hw, hp.wr], contains_addr hd (by omega) hp.scr_fit⟩

theorem scr_in {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 640) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := hp.scr_out hw hd; ⟨r, List.mem_append_right _ hr, hc⟩

theorem st_in {s : State} (hw : s.wr = s₀.wr) {j : Nat} (hj : j < 200) :
    InRegions s.wr (stA s₀ + BitVec.ofNat 64 j) 1 :=
  ⟨stR s₀, by simp [hw, hp.wr], contains_offset (by omega) (by omega)⟩

/-- The words of the scratch space beyond what the permutation uses. -/
theorem hi_sep {d : Nat} (hd₁ : 512 ≤ d) (hd : d + 4 ≤ 640) :
    ∀ r ∈ [reg32 (st s₀) 200, reg32 (scr s₀) 512, stkR s₀], Region.Disjoint ⟨addr (scr s₀) d, 4⟩ r := by
  have := hp.scr_fit
  have hs := sub_word (N := 640) hp.scr_fit hd
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left hs
  · intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    rw [addr_eq (by omega)] at h₁
    have hE := addr_toNat (scr s₀)
    generalize (scr s₀).setWidth 64 = b at *
    bv_omega
  · exact hp.stk_scr.symm.sub_left hs

/-- A word of the scratch space is unchanged by a write to the state. -/
theorem scr_st (m : Mem) {d : Nat} (hd : d + 4 ≤ 640) {j : Nat} (hj : j < 200) (v : Byte) :
    (m.writeW (stA s₀ + BitVec.ofNat 64 j) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
  Mem.readW_writeW_sep (hp.st_scr.symm.sep (contains_addr hd (by omega) hp.scr_fit)
    (contains_offset (by omega) (by omega))) (by decide)

end Pre

/-! ## The two bytes -/

/-- What holds after XORing the two bytes into the state. -/
structure Mid (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ecx : s.gpr .ecx = st s₀
  esi : s.gpr .esi = scr s₀
  edi : s.gpr .edi = s₀.gpr .edi
  ebp : s.gpr .ebp = s₀.gpr .ebp
  esp : s.gpr .esp = E s₀
  sv_ebx : s.mem.readW (addr (scr s₀) 512) 32 = s₀.gpr .ebx
  sv_esi : s.mem.readW (addr (scr s₀) 516) 32 = s₀.gpr .esi
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  state : stateAt s.mem (stA s₀) =
    xorByte (xorByte (stateAt s₀.mem (stA s₀)) (pos s₀) ((arg s₀ 3).setWidth 8)) (rt s₀ - 1) 0x80

theorem wp_xori {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  VG.Proof.Sha256.X86.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem xor_0x80 (b : Byte) : (b.setWidth 32 ^^^ (0x80 : BitVec 32)).setWidth 8 = b ^^^ 0x80 := by
  rw [xor_low]; rfl

theorem bytes_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block padBytes) s₀ (Mid s₀) := by
  have fC := hp.scr_fit; have fS := hp.st_fit
  have hs : (E s₀).toNat + 24 ≤ 2 ^ 32 := hp.sp_fit
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hpl := hp.pos_lt
  unfold padBytes
  refine wp_movm (a := addr (E s₀) 20) (ea_at _ _ _) (hp.arg_in rfl (by omega) (by omega)) fun s₁ u₁ => ?_
  have e1 : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (a := addr (scr s₀) 512) (by rw [ea_at, e1]) (hp.scr_out u₁.wr (by omega)) fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) 516) (by rw [ea_at, u₂.gpr, e1])
    (hp.scr_out (by rw [u₂.wr, u₁.wr]) (by omega)) fun s₃ u₃ => ?_
  have w₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have m₃ : s₃.mem = (s₀.mem.writeW (addr (scr s₀) 512) (s₀.gpr .ebx)).writeW (addr (scr s₀) 516)
      (s₀.gpr .esi) := by
    rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.other .ebx (by decide), u₁.other .esi (by decide)]
  have f₃ : Frame [scR s₀] s₀.mem s₃.mem := by
    rw [m₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) fC)).writeW
      (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) fC)
  have f₃' : Frame [stR s₀, scR s₀] s₀.mem s₃.mem := f₃.mono (by simp)
  refine wp_mov fun s₄ u₄ => ?_
  have k₄ : ∀ r, r ≠ .eax → r ≠ .esi → s₄.gpr r = s₀.gpr r := fun r h h' => by
    rw [u₄.other r h', u₃.gpr, u₂.gpr, u₁.other r h]
  have m₄ : s₄.mem = s₃.mem := u₄.mem
  refine wp_movm (a := addr (E s₀) 4) (by rw [ea_at, k₄ _ (by decide) (by decide)])
    (hp.arg_in (by rw [u₄.wr, w₃]) (by omega) (by omega)) fun s₅ u₅ => ?_
  refine wp_movm (a := addr (E s₀) 8) (by rw [ea_at, u₅.other _ (by decide), k₄ _ (by decide) (by decide)])
    (hp.arg_in (by rw [u₅.wr, u₄.wr, w₃]) (by omega) (by omega)) fun s₆ u₆ => ?_
  refine wp_movm (a := addr (E s₀) 12) (by rw [ea_at, u₆.other _ (by decide), u₅.other _ (by decide),
    k₄ _ (by decide) (by decide)]) (hp.arg_in (by rw [u₆.wr, u₅.wr, u₄.wr, w₃]) (by omega) (by omega))
    fun s₇ u₇ => ?_
  refine wp_add fun s₈ u₈ => ?_
  have m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]
  have w₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, w₃]
  have r₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have c₅ : s₅.gpr .ecx = st s₀ := by rw [u₅.gpr, m₄, hp.arg_keep f₃' (by omega) (by omega)]; rfl
  have a₆ : s₆.gpr .eax = arg s₀ 1 := by
    rw [u₆.gpr, u₅.mem, m₄, hp.arg_keep f₃' (by omega) (by omega)]; rfl
  have d₈ : s₈.gpr .edx = st s₀ + BitVec.ofNat 32 (pos s₀) := by
    rw [u₈.gpr, u₇.gpr, u₇.other _ (by decide), u₆.other _ (by decide), c₅, u₆.mem, u₅.mem, m₄,
      hp.arg_keep f₃' (by omega) (by omega), BitVec.add_comm]
    show _ = _ + BitVec.ofNat 32 (arg s₀ 2).toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  have hpA : addr (s₈.gpr .edx) 0 = stA s₀ + BitVec.ofNat 64 (pos s₀) := by
    rw [d₈]; exact ptr_addr (by omega)
  refine wp_movzx8 (a := stA s₀ + BitVec.ofNat 64 (pos s₀)) (by rw [ea_at, hpA])
    (by rw [r₈, w₈, hp.rd, List.nil_append]; exact hp.st_in rfl (by omega)) fun s₉ u₉ => ?_
  refine wp_xorm (b := .esp) (B := E s₀) (o := 16)
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), k₄ _ (by decide) (by decide)])
    (hp.arg_in (by rw [u₉.wr, w₈]) (by omega) (by omega)) fun s₁₀ u₁₀ => ?_
  refine wp_store8 (r := .bl) (a := stA s₀ + BitVec.ofNat 64 (pos s₀))
    (by rw [ea_at, u₁₀.other _ (by decide), u₉.other _ (by decide), hpA])
    (by rw [u₁₀.wr, u₉.wr, w₈]; exact hp.st_in rfl (by omega)) fun s₁₁ u₁₁ => ?_
  have m₁₁ : s₁₁.mem = s₃.mem.writeW (stA s₀ + BitVec.ofNat 64 (pos s₀))
      (s₃.mem (stA s₀ + BitVec.ofNat 64 (pos s₀)) ^^^ (arg s₀ 3).setWidth 8) := by
    rw [u₁₁.mem, show Reg8.bl.reg = Reg.ebx from rfl, u₁₀.gpr, u₉.gpr, u₁₀.mem, u₉.mem, m₈, xor_low,
      hp.arg_keep f₃' (by omega) (by omega)]
    rfl
  refine wp_mov fun s₁₂ u₁₂ => wp_add fun s₁₃ u₁₃ => wp_subi fun s₁₄ u₁₄ _ => ?_
  have d₁₄ : s₁₄.gpr .edx = st s₀ + BitVec.ofNat 32 (rt s₀ - 1) := by
    rw [u₁₄.gpr, u₁₃.gpr, u₁₂.gpr, u₁₂.other .eax (by decide), u₁₁.gpr, u₁₀.other .ecx (by decide),
      u₁₀.other .eax (by decide), u₉.other .ecx (by decide), u₉.other .eax (by decide),
      u₈.other .ecx (by decide), u₈.other .eax (by decide), u₇.other .ecx (by decide),
      u₇.other .eax (by decide), u₆.other .ecx (by decide), c₅, a₆]
    have h72 : 72 ≤ (arg s₀ 1).toNat := hr₀
    show _ = _ + BitVec.ofNat 32 ((arg s₀ 1).toNat - 1)
    exact Offset.add_sub_one32 _ _ (by omega)
  have hpB : addr (s₁₄.gpr .edx) 0 = stA s₀ + BitVec.ofNat 64 (rt s₀ - 1) := by
    rw [d₁₄]; exact ptr_addr (by omega)
  have w₁₄ : s₁₄.wr = s₀.wr := by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, w₈]
  refine wp_movzx8 (a := stA s₀ + BitVec.ofNat 64 (rt s₀ - 1)) (by rw [ea_at, hpB])
    (by
      rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, r₈, w₁₄, hp.rd, List.nil_append]
      exact hp.st_in rfl (by omega)) fun s₁₅ u₁₅ => ?_
  refine wp_xori fun s₁₆ u₁₆ => ?_
  refine wp_store8 (r := .bl) (a := stA s₀ + BitVec.ofNat 64 (rt s₀ - 1))
    (by rw [ea_at, u₁₆.other _ (by decide), u₁₅.other _ (by decide), hpB])
    (by rw [u₁₆.wr, u₁₅.wr, w₁₄]; exact hp.st_in rfl (by omega)) fun s₁₇ u₁₇ => WP.block_nil ?_
  have m₁₄ : s₁₄.mem = s₁₁.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem]
  have m₁₇ : s₁₇.mem = s₁₁.mem.writeW (stA s₀ + BitVec.ofNat 64 (rt s₀ - 1))
      (s₁₁.mem (stA s₀ + BitVec.ofNat 64 (rt s₀ - 1)) ^^^ 0x80) := by
    rw [u₁₇.mem, show Reg8.bl.reg = Reg.ebx from rfl, u₁₆.gpr, u₁₅.gpr, u₁₆.mem, u₁₅.mem, m₁₄, xor_0x80]
  have f₁₇ : Frame [stR s₀, scR s₀] s₃.mem s₁₇.mem := by
    rw [m₁₇, m₁₁]
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (contains_offset (by omega) (by omega))).writeW
      (List.mem_cons_self ..) _ (contains_offset (by omega) (by omega))
  have k₁₇ : ∀ r, r ∉ [Reg.eax, .ebx, .ecx, .edx, .esi] → s₁₇.gpr r = s₀.gpr r := fun r hr => by
    have ⟨a, b, c, d, e⟩ : r ≠ .eax ∧ r ≠ .ebx ∧ r ≠ .ecx ∧ r ≠ .edx ∧ r ≠ .esi := by simpa using hr
    rw [u₁₇.gpr, u₁₆.other r b, u₁₅.other r b, u₁₄.other r d, u₁₃.other r d, u₁₂.other r d, u₁₁.gpr,
      u₁₀.other r b, u₉.other r b, u₈.other r d, u₇.other r d, u₆.other r a, u₅.other r c, k₄ r a e]
  have hsc : ∀ d, d + 4 ≤ 640 → s₁₇.mem.readW (addr (scr s₀) d) 32 = s₃.mem.readW (addr (scr s₀) d) 32 :=
    fun d hd => by rw [m₁₇, hp.scr_st _ hd (by omega), m₁₁, hp.scr_st _ hd (by omega)]
  refine ⟨?_, by rw [u₁₇.wr, u₁₆.wr, u₁₅.wr, w₁₄], ?_, ?_, k₁₇ _ (by decide), k₁₇ _ (by decide),
    k₁₇ _ (by decide), ?_, ?_, f₃'.trans f₁₇, ?_⟩
  · rw [u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, r₈]
  · rw [u₁₇.gpr, u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide),
      u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), c₅]
  · rw [u₁₇.gpr, u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide),
      u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, e1]
  · rw [hsc _ (by omega), m₃, word_sep (N := 640) fC (by omega) (by omega) (by omega),
      Mem.readW_writeW_self32]
  · rw [hsc _ (by omega), m₃, Mem.readW_writeW_self32]
  · have e₃ : stateAt s₃.mem (stA s₀) = stateAt s₀.mem (stA s₀) :=
      Proof.Sha3.stateAt_congr fun i hi => f₃.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi
    rw [← e₃, ← stateAt_xorByte (m := s₃.mem) (m' := s₁₁.mem) (by omega)
      (by rw [m₁₁, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)])
      (fun i hi hne => by
        rw [m₁₁, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (ne_of_lt200 hi (by omega) hne))])]
    exact stateAt_xorByte (by omega)
      (by rw [m₁₇, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)])
      (fun i hi hne => by
        rw [m₁₇, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (ne_of_lt200 hi (by omega) hne))])

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa pad s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.padX86.post s₀ s' := by
  have fC := hp.scr_fit; have fS := hp.st_fit
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have h72 : 72 ≤ (arg s₀ 1).toNat := hr₀
  have h168 : (arg s₀ 1).toNat ≤ 168 := hr₁
  unfold pad
  refine WP.seq (WP.mono (bytes_ok hp) fun s₁ h => ?_)
  refine WP.seq (permuteCall_ok (st := .ecx) (scr := .esi) (by decide) (by decide) h.esp h.ecx h.esi
    hp.sp_lo fS (by omega) (hp.st_scr.sub_right (Region.sub_prefix (by omega))) hp.stk_st
    (hp.stk_scr.sub_right (Region.sub_prefix (by omega))) (by rw [h.wr, hp.wr]; simp)
    (by rw [h.wr, hp.wr]; simp) fun s₂ rd₂ wr₂ cs₂ f₂ e₂ => ?_)
  have w₂ : s₂.wr = s₀.wr := wr₂.trans h.wr
  have hsi : s₂.gpr .esi = scr s₀ := by rw [cs₂ _ (by decide), h.esi]
  refine wp_movm (a := addr (scr s₀) 512) (by rw [ea_at, hsi]) (hp.scr_in w₂ (by omega)) fun s₃ u₃ => ?_
  refine wp_movm (a := addr (scr s₀) 516) (by rw [ea_at, u₃.other _ (by decide), hsi])
    (hp.scr_in (by rw [u₃.wr, w₂]) (by omega)) fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have hk : ∀ d, 512 ≤ d → d + 4 ≤ 640 → s₂.mem.readW (addr (scr s₀) d) 32 = s₁.mem.readW (addr (scr s₀) d) 32 :=
    fun d h1 h2 => f₂.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _)
      (hp.hi_sep h1 h2) (by decide)
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg hR hm => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), u₃.gpr, hk _ (by omega) (by omega), h.sv_ebx]
    · rw [u₄.gpr, u₃.mem, hk _ (by omega) (by omega), h.sv_esi]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), cs₂ _ (by decide), h.edi]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), cs₂ _ (by decide), h.ebp]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), cs₂ _ (by decide), h.esp]
  · rw [m₄]
    have hf : Frame [stR s₀, scR s₀, stkR s₀] s₀.mem s₂.mem :=
      (h.frame.mono fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp).trans (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨stR s₀, by simp, fun _ h => h⟩
        · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
        · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
    exact hf.readW (Region.contains_self _ _)
      (by simpa using ⟨hp.ret_st, hp.ret_scr, ret_stk (E := E s₀) (by have := hp.sp_fit; omega) hp.sp_lo⟩)
      (by decide)
  · rw [m₄, show (arg s₀ 0).setWidth 64 = stA s₀ from rfl, e₂, h.state,
      absorb_pad (by omega) (by omega), ← hm, show Rep (rt s₀) msg = stateAt s₀.mem (stA s₀) from hR.symm]

/-! ## Constant time -/

/-- The initial taint: `esp` is public, and points `4` bytes below the
arguments (writable region 2), which are public; the words of `state` and
`scratch` are the base addresses of regions 0 and 1. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [200, 640, 20], bases := [(.esp, 2, 4)],
    slots := [(2, 0, 20)], wbases := [(2, 0, 0), (2, 16, 1)], room := 12 }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hst := hp.st_fit; have hsc := hp.scr_fit
  have hs : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 := hp.sp_fit
  have hlo : 12 ≤ (s.gpr .esp).toNat := hp.sp_lo
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩ fun _ => ⟨hlo, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_scr, hp.a_st.symm⟩, hp.a_scr.symm, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · simp only [addr_toNat]; omega
    · simp only [addr_toNat]; omega
    · show (addr (s.gpr .esp) 4).toNat + 20 ≤ 2 ^ 32
      rw [addr_eq (by omega), BitVec.toNat_add, addr_toNat, BitVec.toNat_ofNat]; omega
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'
    show addr (s.gpr .esp) 4 = (VG.X86.Taint.region s 2).base
    rw [VG.X86.Taint.region, hp.wr]; rfl
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 0) 32) 0 = stA s
      simp [addr, st, arg, argAddr]
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 16) 32) 0 = (scr s).setWidth 64
      rw [argWord_eq (n := 20) (by omega) (k := 16) (by omega)]
      simp [addr, scr, arg]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have e : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 τ₀.room, τ₀.room⟩ : Region) = stkR s :=
      (stk_eq hlo).symm
    rw [e]
    rintro r (rfl | rfl | rfl)
    · exact hp.stk_st
    · exact hp.stk_scr
    · exact (arg_stk (n := 20) (by omega) hlo).symm

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.padX86.pre s₁) (h₂ : Proof.Sha3.padX86.pre s₂)
    (hpub : Proof.Sha3.padX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [stR, scR, argR, stA, st, scr, argAddr, ha 0 (by omega), ha 4 (by omega), hesp]
  · intro sl hsl
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl; decide
  · intro sl hsl k _ hk
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl
    simp only [Nat.zero_add] at hk
    simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp₁.wr, hp₂.wr]
    show s₁.mem (addr (s₁.gpr .esp) 4 + BitVec.ofNat 64 k) = s₂.mem (addr (s₂.gpr .esp) 4 + BitVec.ofNat 64 k)
    rw [argWord_eq (n := 20) (by have := hp₁.sp_fit; omega) hk,
      argWord_eq (n := 20) (by have := hp₂.sp_fit; omega) hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-- Memory holding the arguments `0x1000, 72, 0, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4008 then 72 else if a = 0x4015 then 0x30 else 0

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩, ⟨0x4004, 20⟩]

theorem sat_pre : Proof.Sha3.padX86.pre sat := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a1 : arg sat 1 = 72 := by decide
  have a2 : arg sat 2 = 0 := by decide
  have a4 : arg sat 4 = 0x3000 := by decide
  have e : argAddr sat 0 = 0x4004 := by decide
  simp only [Proof.Sha3.padX86, a0, a1, a2, a4, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
    by decide⟩ <;>
  · exact Region.disjoint_of_sep (by decide)

theorem pad_verified : Verified X86.target pad Proof.Sha3.padX86 := by
  refine ⟨fun s hs => correct (pre_of hs), ?_, ⟨sat, sat_pre⟩⟩
  exact VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide_weak VG.Proof.Sha3.X86.dropRC)

end VG.Proof.Sha3.X86.Stream.Pad
