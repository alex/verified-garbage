import VerifiedGarbage.Proof.Sha3.X86.Permute
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The SHA-3 sponge on x86 (32-bit): `squeeze`

Untrusted: everything here is checked by Lean. The structure of the x86-64
proof (`VG.Proof.Sha3.X86_64.Stream.Squeeze`), with `state` in `ebx`,
`scratch` in `ebp`, `out` in `esi`, the bytes left in `edi`, and
`state + pos` and `rate` in the scratch space.
-/

namespace VG.Proof.Sha3.X86.Stream.Squeeze

open VG VG.X86 VG.Impl.Sha3.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movm wp_movzx8 wp_store wp_store8 wp_add
  wp_addi wp_sub wp_subi wp_cmp wp_test contains_addr addr_toNat)
open VG.Proof.Sha3.X86 (permuteCall_ok reg32)
open VG.Proof.Sha3 (byteOf byteOf_stateAt iterF iterF_succ length_squeezeFrom squeezeFrom_getElem
  squeezeFrom_iterF writeW8_self writeW8_other rate_bounds contains_offset div_mod_eq)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev rt : Nat := (arg s₀ 1).toNat
abbrev pos₀ : Nat := (arg s₀ 2).toNat
abbrev op : BitVec 32 := arg s₀ 3
abbrev outn : Nat := (arg s₀ 4).toNat
abbrev scr : BitVec 32 := arg s₀ 5
abbrev stA : Addr := (st s₀).setWidth 64
abbrev oA : Addr := (op s₀).setWidth 64
abbrev stR : Region := ⟨stA s₀, 200⟩
abbrev oR : Region := ⟨oA s₀, outn s₀⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 640⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 12
/-- The initial state. -/
abbrev S₀ : Spec.Sha3.State := stateAt s₀.mem (stA s₀)

/-- The caller's callee-saved registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop := ∀ p ∈ saved, m.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, oR s₀, scR s₀, argR s₀]
  st_o : (stR s₀).Disjoint (oR s₀)
  st_scr : (stR s₀).Disjoint (scR s₀)
  o_scr : (oR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_o : (argR s₀).Disjoint (oR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_o : (retR s₀).Disjoint (oR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_o : (stkR s₀).Disjoint (oR s₀)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + 200 ≤ 2 ^ 32
  o_fit : (op s₀).toNat + outn s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 640 ≤ 2 ^ 32
  sp_lo : 12 ≤ (E s₀).toNat
  sp_fit : (E s₀).toNat + 28 ≤ 2 ^ 32
  rate : rt s₀ ∈ rates
  pos_le : pos₀ s₀ ≤ rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.squeezeX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩ := h
  have e := stk_eq h18
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by show (below _ _).Disjoint _; rw [e]; exact h12,
    by show (below _ _).Disjoint _; rw [e]; exact h13, by show (below _ _).Disjoint _; rw [e]; exact h14,
    h15, h16, h17, h18, h19, h20, h21⟩

theorem outn_lt (s₀ : State) : outn s₀ < 2 ^ 32 := (arg s₀ 4).isLt

theorem argR_eq (s₀ : State) : argR s₀ = ⟨addr (E s₀) 4, 24⟩ := rfl

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem rt_pos : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  have := rate_bounds hp.rate; omega

theorem arg_in {s : State} (hw : s.wr = s₀.wr) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 28) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) d) 4 :=
  ⟨argR s₀, by simp [hw, hp.wr], by rw [argR_eq s₀]; exact arg_contains (by have := hp.sp_fit; omega) h₁ h₂⟩

/-- The argument words are never written. -/
theorem arg_keep {m : Mem} (hf : Frame [scR s₀] s₀.mem m) {d : Nat} (h₁ : 4 ≤ d)
    (h₂ : d + 4 ≤ 28) : m.readW (addr (E s₀) d) 32 = s₀.mem.readW (addr (E s₀) d) 32 := by
  have fit : (E s₀).toNat + 4 + 24 ≤ 2 ^ 32 := by have := hp.sp_fit; omega
  have hs := arg_word fit h₁ h₂
  refine hf.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact (argR_eq s₀ ▸ hp.a_scr).sub_left hs

theorem scr_out {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 640) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hw, hp.wr], contains_addr hd (by omega) hp.scr_fit⟩

theorem scr_in {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 640) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := hp.scr_out hw hd; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A write within the scratch space. -/
theorem frame_scr {rs : List Region} (hr : scR s₀ ∈ rs) {m : Mem} {m₀ : Mem} (hf : Frame rs m₀ m) {d : Nat}
    (hd : d + 4 ≤ 640) (v : BitVec 32) : Frame rs m₀ (m.writeW (addr (scr s₀) d) v) :=
  hf.writeW hr _ (contains_addr hd (by omega) hp.scr_fit)

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

/-- A word of the scratch space is unchanged by a write to `out`. -/
theorem scr_o (m : Mem) {d : Nat} (hd : d + 4 ≤ 640) {j : Nat} (hj : j < outn s₀) (v : Byte) :
    (m.writeW (oA s₀ + BitVec.ofNat 64 j) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
  Mem.readW_writeW_sep (hp.o_scr.symm.sep (contains_addr hd (by omega) hp.scr_fit)
    (contains_offset (by omega) (by have := outn_lt s₀; omega))) (by decide)

end Pre

theorem Saved.keep {s₀ : State} {m m' : Mem} (hs : Saved s₀ m)
    (hk : ∀ d, 512 ≤ d → d + 4 ≤ 528 → m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32) :
    Saved s₀ m' := fun p hp' => by
  have ⟨h1, h2⟩ : 512 ≤ p.2 ∧ p.2 + 4 ≤ 528 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp
  rw [hk _ h1 h2]; exact hs p hp'

/-! ## The loop invariant -/

/-- After `i` bytes of output, `k` permutations and `pos` bytes of the
current block: `pos₀ + i = rate * k + pos`. -/
structure Inv (s₀ : State) (i k pos : Nat) (s : State) : Prop where
  i_le : i ≤ outn s₀
  hi : pos₀ s₀ + i = rt s₀ * k + pos
  pos_le : pos ≤ rt s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = E s₀
  esi : s.gpr .esi = op s₀ + BitVec.ofNat 32 i
  edi : s.gpr .edi = BitVec.ofNat 32 (outn s₀ - i)
  ptr : s.mem.readW (addr (scr s₀) 528) 32 = st s₀ + BitVec.ofNat 32 pos
  rate : s.mem.readW (addr (scr s₀) 532) 32 = arg s₀ 1
  frame : Frame [stR s₀, oR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  state : stateAt s.mem (stA s₀) = iterF k (S₀ s₀)
  out : ∀ j < i, s.mem (oA s₀ + BitVec.ofNat 64 j) =
    byteOf (iterF ((pos₀ s₀ + j) / rt s₀) (S₀ s₀)) ((pos₀ s₀ + j) % rt s₀)

theorem Inv.congr {s₀ : State} {i k pos : Nat} {s s' : State} (h : Inv s₀ i k pos s)
    (hg : ∀ r ∈ [Reg.ebx, .ebp, .esp, .esi, .edi], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ i k pos s' where
  i_le := h.i_le
  hi := h.hi
  pos_le := h.pos_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by simp)]; exact h.ebx
  ebp := by rw [hg _ (by simp)]; exact h.ebp
  esp := by rw [hg _ (by simp)]; exact h.esp
  esi := by rw [hg _ (by simp)]; exact h.esi
  edi := by rw [hg _ (by simp)]; exact h.edi
  ptr := by rw [hm]; exact h.ptr
  rate := by rw [hm]; exact h.rate
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  state := by rw [hm]; exact h.state
  out := by rw [hm]; exact h.out

/-! ## The prologue -/

theorem setup_eq : setup = [.mov .eax (.mem (at_ .esp 24)), .store (at_ .eax 512) .ebx,
    .store (at_ .eax 516) .esi, .store (at_ .eax 520) .edi, .store (at_ .eax 524) .ebp,
    .mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .esp 12)),
    .alu .add .ecx (.reg .ebx), .store (at_ .ebp 528) .ecx, .mov .ecx (.mem (at_ .esp 8)),
    .store (at_ .ebp 532) .ecx, .mov .esi (.mem (at_ .esp 16)), .mov .edi (.mem (at_ .esp 20)),
    .alu .test .edi (.reg .edi)] := rfl

/-- The memory after saving the registers. -/
def saveMem (s₀ : State) : Mem :=
  (((s₀.mem.writeW (addr (scr s₀) 512) (s₀.gpr .ebx)).writeW (addr (scr s₀) 516) (s₀.gpr .esi)).writeW
    (addr (scr s₀) 520) (s₀.gpr .edi)).writeW (addr (scr s₀) 524) (s₀.gpr .ebp)

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) s₀ fun s => Inv s₀ 0 0 (pos₀ s₀) s ∧ s.zf = some (decide (outn s₀ = 0)) := by
  have fC := hp.scr_fit
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hpl := hp.pos_le
  have sep := fun (m : Mem) (v : BitVec 32) (d e : Nat) (hd : d + 4 ≤ 640) (he : e + 4 ≤ 640)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) => word_sep (b := scr s₀) (N := 640) fC hd he h m v
  rw [setup_eq]
  refine wp_movm (a := addr (E s₀) 24) (ea_at _ _ _) (hp.arg_in rfl (by omega) (by omega)) fun s₁ u₁ => ?_
  have e1 : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (a := addr (scr s₀) 512) (by rw [ea_at, e1]) (hp.scr_out u₁.wr (by omega)) fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) 516) (by rw [ea_at, u₂.gpr, e1])
    (hp.scr_out (by rw [u₂.wr, u₁.wr]) (by omega)) fun s₃ u₃ => ?_
  refine wp_store (a := addr (scr s₀) 520) (by rw [ea_at, u₃.gpr, u₂.gpr, e1])
    (hp.scr_out (by rw [u₃.wr, u₂.wr, u₁.wr]) (by omega)) fun s₄ u₄ => ?_
  refine wp_store (a := addr (scr s₀) 524) (by rw [ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e1])
    (hp.scr_out (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by omega)) fun s₅ u₅ => ?_
  have g₅ : ∀ r, r ≠ .eax → s₅.gpr r = s₀.gpr r := fun r h => by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r h]
  have m₅ : s₅.mem = saveMem s₀ := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide),
      u₁.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide)]; rfl
  have w₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have r₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hsc : scR s₀ ∈ [scR s₀] := List.mem_singleton_self _
  have f₅ : Frame [scR s₀] s₀.mem s₅.mem := by
    rw [m₅]
    exact hp.frame_scr hsc (hp.frame_scr hsc (hp.frame_scr hsc (hp.frame_scr hsc (Frame.refl _ _)
      (by omega) _) (by omega) _) (by omega) _) (by omega) _
  have sv₅ : Saved s₀ s₅.mem := by
    intro p hp'
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [m₅]
    rcases hp' with rfl | rfl | rfl | rfl
    · simp only [saveMem]
      rw [sep _ _ 512 524 (by omega) (by omega) (by omega), sep _ _ 512 520 (by omega) (by omega) (by omega),
        sep _ _ 512 516 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
    · simp only [saveMem]
      rw [sep _ _ 516 524 (by omega) (by omega) (by omega), sep _ _ 516 520 (by omega) (by omega) (by omega),
        Mem.readW_writeW_self32]
    · simp only [saveMem]
      rw [sep _ _ 520 524 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
    · simp only [saveMem]; rw [Mem.readW_writeW_self32]
  refine wp_mov fun s₆ u₆ => ?_
  refine wp_movm (a := addr (E s₀) 4) (by rw [ea_at, u₆.other _ (by decide), g₅ _ (by decide)])
    (hp.arg_in (by rw [u₆.wr, w₅]) (by omega) (by omega)) fun s₇ u₇ => ?_
  refine wp_movm (a := addr (E s₀) 12) (by rw [ea_at, u₇.other _ (by decide), u₆.other _ (by decide),
    g₅ _ (by decide)]) (hp.arg_in (by rw [u₇.wr, u₆.wr, w₅]) (by omega) (by omega)) fun s₈ u₈ => ?_
  refine wp_add fun s₉ u₉ => ?_
  have e5 : s₅.gpr .eax = scr s₀ := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, e1]
  have hb₉ : s₉.gpr .ebp = scr s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, e5]
  have m₈ : s₈.mem = s₅.mem := by rw [u₈.mem, u₇.mem, u₆.mem]
  have hst : s₇.gpr .ebx = st s₀ := by
    rw [u₇.gpr, u₆.mem, hp.arg_keep f₅ (by omega) (by omega)]; rfl
  have hpos : s₉.gpr .ecx = st s₀ + BitVec.ofNat 32 (pos₀ s₀) := by
    rw [u₉.gpr, u₈.gpr, u₈.other _ (by decide), hst, u₇.mem, u₆.mem, hp.arg_keep f₅ (by omega) (by omega),
      BitVec.add_comm]
    show _ = _ + BitVec.ofNat 32 (arg s₀ 2).toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  refine wp_store (a := addr (scr s₀) 528) (by rw [ea_at, hb₉])
    (hp.scr_out (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]) (by omega)) fun s₁₀ u₁₀ => ?_
  have f₁₀ : Frame [scR s₀] s₀.mem s₁₀.mem := by
    rw [u₁₀.mem, u₉.mem, m₈]; exact hp.frame_scr hsc f₅ (by omega) _
  refine wp_movm (a := addr (E s₀) 8) (by rw [ea_at, u₁₀.gpr, u₉.other _ (by decide),
    u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide)])
    (hp.arg_in (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]) (by omega) (by omega)) fun s₁₁ u₁₁ => ?_
  refine wp_store (a := addr (scr s₀) 532) (by rw [ea_at, u₁₁.other _ (by decide), u₁₀.gpr, hb₉])
    (hp.scr_out (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]) (by omega)) fun s₁₂ u₁₂ => ?_
  have f₁₂ : Frame [scR s₀] s₀.mem s₁₂.mem := by
    rw [u₁₂.mem, u₁₁.mem]; exact hp.frame_scr hsc f₁₀ (by omega) _
  have hw₁₂ : s₁₂.wr = s₀.wr := by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]
  refine wp_movm (a := addr (E s₀) 16) (by rw [ea_at, u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr,
    u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
    g₅ _ (by decide)]) (hp.arg_in hw₁₂ (by omega) (by omega)) fun s₁₃ u₁₃ => ?_
  refine wp_movm (a := addr (E s₀) 20) (by rw [ea_at, u₁₃.other _ (by decide), u₁₂.gpr,
    u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
    u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide)])
    (hp.arg_in (by rw [u₁₃.wr, hw₁₂]) (by omega) (by omega)) fun s₁₄ u₁₄ => ?_
  refine wp_test fun s₁₅ u₁₅ z₁₅ => WP.block_nil ?_
  -- The registers and memory at the end.
  have g : ∀ r, r ∉ [Reg.eax, .ebp, .ebx, .ecx, .esi, .edi] → s₁₅.gpr r = s₀.gpr r := fun r hr => by
    have ⟨a, b, c', d, e, f⟩ : r ≠ .eax ∧ r ≠ .ebp ∧ r ≠ .ebx ∧ r ≠ .ecx ∧ r ≠ .esi ∧ r ≠ .edi := by
      simpa using hr
    rw [u₁₅.gpr, u₁₄.other r f, u₁₃.other r e, u₁₂.gpr, u₁₁.other r d, u₁₀.gpr, u₉.other r d,
      u₈.other r d, u₇.other r c', u₆.other r b, g₅ r a]
  have hm : s₁₅.mem = s₁₂.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem]
  have hm₁₂ : s₁₂.mem = (s₁₀.mem.writeW (addr (scr s₀) 532) (s₁₁.gpr .ecx)) := by
    rw [u₁₂.mem, u₁₁.mem]
  have hrate : s₁₁.gpr .ecx = arg s₀ 1 := by
    rw [u₁₁.gpr, hp.arg_keep f₁₀ (by omega) (by omega)]; rfl
  have hdi : s₁₄.gpr .edi = arg s₀ 4 := by
    rw [u₁₄.gpr, u₁₃.mem, hp.arg_keep f₁₂ (by omega) (by omega)]; rfl
  refine ⟨⟨Nat.zero_le _, by simp, hpl, ?_, by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, hw₁₂], ?_, ?_, g .esp (by decide),
    ?_, ?_, ?_, ?_, by rw [hm]; exact f₁₂.mono (by simp), ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩,
    ?_⟩
  · rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, r₅]
  · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), hst]
  · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.gpr, hb₉]
  · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.gpr, hp.arg_keep f₁₂ (by omega) (by omega), BitVec.add_zero]
    rfl
  · rw [u₁₅.gpr, hdi, Nat.sub_zero]; simp [outn]
  · rw [hm, hm₁₂, sep _ _ 528 532 (by omega) (by omega) (by omega), u₁₀.mem, Mem.readW_writeW_self32]
    exact hpos
  · rw [hm, hm₁₂, Mem.readW_writeW_self32, hrate]
  · rw [hm, hm₁₂]
    refine sv₅.keep fun d h1 h2 => ?_
    rw [sep _ _ d 532 (by omega) (by omega) (by omega), u₁₀.mem, u₉.mem, m₈,
      sep _ _ d 528 (by omega) (by omega) (by omega)]
  · rw [hm]
    exact Proof.Sha3.stateAt_congr fun i hi => f₁₂.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi
  · rw [z₁₅, hdi, BitVec.and_self]
    rw [show arg s₀ 4 = BitVec.ofNat 32 (outn s₀) by simp [outn],
      VG.Proof.Sha256.X86.Stream.ofNat_beq_zero (outn_lt s₀)]

/-! ## One iteration -/

theorem check_eq : loadVars ++ atEnd = [.mov .ecx (.mem (at_ .ebp 528)), .mov .edx (.mem (at_ .ebp 532)),
    .mov .eax (.reg .ecx), .alu .sub .eax (.reg .ebx), .alu .cmp .eax (.reg .edx)] := rfl

/-- Test whether the block is used up. -/
theorem check_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s) :
    WP isa (.block (loadVars ++ atEnd)) s fun s' =>
      Inv s₀ i k pos s' ∧ s'.zf = some (decide (pos = rt s₀)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hpl := hI.pos_le
  rw [check_eq]
  refine wp_movm (a := addr (scr s₀) 528) (by rw [ea_at, hI.ebp]) (hp.scr_in hI.wr (by omega))
    fun s₁ u₁ => ?_
  refine wp_movm (a := addr (scr s₀) 532) (by rw [ea_at, u₁.other _ (by decide), hI.ebp])
    (hp.scr_in (by rw [u₁.wr, hI.wr]) (by omega)) fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => wp_sub fun s₄ u₄ _ => wp_cmp fun s₅ u₅ _ z₅ => WP.block_nil ?_
  have g : ∀ r, r ∉ [Reg.ecx, .edx, .eax] → s₅.gpr r = s.gpr r := fun r hr => by
    have ⟨a, b, c⟩ : r ≠ .ecx ∧ r ≠ .edx ∧ r ≠ .eax := by simpa using hr
    rw [u₅.gpr, u₄.other r c, u₃.other r c, u₂.other r b, u₁.other r a]
  refine ⟨hI.congr (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
    (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]), ?_⟩
  have hax : s₄.gpr .eax = BitVec.ofNat 32 pos := by
    rw [u₄.gpr, u₃.gpr, u₃.other .ebx (by decide), u₂.other .ecx (by decide), u₂.other .ebx (by decide),
      u₁.gpr, u₁.other .ebx (by decide), hI.ptr, hI.ebx, add_sub_self]
  have hdx : s₄.gpr .edx = BitVec.ofNat 32 (rt s₀) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, hI.rate]
    simp [rt]
  rw [z₅, hax, hdx, VG.Proof.Sha256.X86.Stream.sub_beq (by omega) (by omega)]

theorem permute_ok {s₀ : State} (hp : Pre s₀) {i k : Nat} {s : State} (hI : Inv s₀ i k (rt s₀) s) :
    WP isa (.seq (.block [.store (at_ .ebp pOff) .ebx]) (permuteCall .ebx .ebp)) s (Inv s₀ i (k + 1) 0) := by
  have fC := hp.scr_fit
  refine WP.seq (wp_store (a := addr (scr s₀) 528) (by rw [ea_at, hI.ebp]; rfl)
    (hp.scr_out hI.wr (by omega)) fun s₁ u₁ => WP.block_nil ?_)
  have hwr : s₁.wr = s₀.wr := u₁.wr.trans hI.wr
  have e₁ : ∀ r, s₁.gpr r = s.gpr r := fun r => by rw [u₁.gpr]
  refine permuteCall_ok (st := .ebx) (scr := .ebp) (by decide) (by decide) (by rw [e₁, hI.esp])
    (by rw [e₁, hI.ebx]) (by rw [e₁, hI.ebp]) hp.sp_lo hp.st_fit (by omega)
    (hp.st_scr.sub_right (Region.sub_prefix (by omega))) hp.stk_st
    (hp.stk_scr.sub_right (Region.sub_prefix (by omega))) (by rw [hwr, hp.wr]; simp)
    (by rw [hwr, hp.wr]; simp) fun s' rd' wr' cs' hf hst => ?_
  have hd : ∀ r ∈ [reg32 (st s₀) 200, reg32 (scr s₀) 512, stkR s₀], (oR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_o.symm
    · exact hp.o_scr.sub_right (Region.sub_prefix (by omega))
    · exact hp.stk_o.symm
  have hfw : Frame [scR s₀] s.mem s₁.mem := by
    rw [u₁.mem]; exact hp.frame_scr (List.mem_singleton_self _) (Frame.refl _ _) (by omega) _
  have keep : ∀ d, 512 ≤ d → d + 4 ≤ 640 →
      s'.mem.readW (addr (scr s₀) d) 32 = s₁.mem.readW (addr (scr s₀) d) 32 := fun d h1 h2 =>
    hf.readW (Region.contains_self _ _) (hp.hi_sep h1 h2) (by decide)
  refine ⟨hI.i_le, by rw [hI.hi, Nat.mul_succ]; rfl, Nat.zero_le _, rd'.trans (u₁.rd.trans hI.rd),
    wr'.trans hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cs' _ (by decide), e₁, hI.ebx]
  · rw [cs' _ (by decide), e₁, hI.ebp]
  · rw [cs' _ (by decide), e₁, hI.esp]
  · rw [cs' _ (by decide), e₁, hI.esi]
  · rw [cs' _ (by decide), e₁, hI.edi]
  · rw [keep 528 (by omega) (by omega), u₁.mem, Mem.readW_writeW_self32, hI.ebx]; simp
  · rw [keep 532 (by omega) (by omega), u₁.mem, word_sep (N := 640) fC (by omega) (by omega) (by omega)]
    exact hI.rate
  · refine hI.frame.trans ((hfw.mono (by simp)).trans (hf.sub fun r hr => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · refine hI.saved.keep fun d h1 h2 => ?_
    rw [keep d h1 (by omega), u₁.mem, word_sep (N := 640) fC (by omega) (by omega) (by omega)]
  · rw [hst, show stateAt s₁.mem (stA s₀) = stateAt s.mem (stA s₀) from
      Proof.Sha3.stateAt_congr fun i hi => hfw.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi,
      hI.state, iterF_succ]
  · intro j hj
    have hj' : j < outn s₀ := by have := hI.i_le; omega
    rw [hf.bytes (R := oR s₀) hd (by have := outn_lt s₀; show outn s₀ ≤ 2 ^ 64; omega) hj',
      hfw.bytes (R := oR s₀) (by simpa using hp.o_scr) (by have := outn_lt s₀; show outn s₀ ≤ 2 ^ 64; omega) hj']
    exact hI.out j hj

theorem store_eq : loadVars ++ squeezeByte ++ storeVars ++ step =
    [.mov .ecx (.mem (at_ .ebp 528)), .mov .edx (.mem (at_ .ebp 532)), .movzx8 .eax (at_ .ecx 0),
      .store8 (at_ .esi 0) .al, .alu .add .ecx (.imm 1), .store (at_ .ebp 528) .ecx,
      .store (at_ .ebp 532) .edx, .alu .add .esi (.imm 1), .alu .sub .edi (.imm 1)] := rfl

theorem store_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hlt : pos < rt s₀) (hi : i < outn s₀) :
    WP isa (.block (loadVars ++ squeezeByte ++ storeVars ++ step)) s fun s' =>
      Inv s₀ (i + 1) k (pos + 1) s' ∧ s'.zf = some (decide (outn s₀ - (i + 1) = 0)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hn := outn_lt s₀
  have fC := hp.scr_fit; have fS := hp.st_fit; have fO := hp.o_fit
  have sep := fun (m : Mem) (v : BitVec 32) (d e : Nat) (hd : d + 4 ≤ 640) (he : e + 4 ≤ 640)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) => word_sep (b := scr s₀) (N := 640) fC hd he h m v
  rw [store_eq]
  refine wp_movm (a := addr (scr s₀) 528) (by rw [ea_at, hI.ebp]) (hp.scr_in hI.wr (by omega))
    fun s₁ u₁ => ?_
  refine wp_movm (a := addr (scr s₀) 532) (by rw [ea_at, u₁.other _ (by decide), hI.ebp])
    (hp.scr_in (by rw [u₁.wr, hI.wr]) (by omega)) fun s₂ u₂ => ?_
  have e₂ : s₂.gpr .ecx = st s₀ + BitVec.ofNat 32 pos := by rw [u₂.other _ (by decide), u₁.gpr, hI.ptr]
  have d₂ : s₂.gpr .edx = arg s₀ 1 := by rw [u₂.gpr, u₁.mem]; exact hI.rate
  have hsA : addr (st s₀ + BitVec.ofNat 32 pos) 0 = stA s₀ + BitVec.ofNat 64 pos := ptr_addr (by omega)
  refine wp_movzx8 (a := stA s₀ + BitVec.ofNat 64 pos) (by rw [ea_at, e₂, hsA])
    ⟨stR s₀, by simp [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hI.rd, hI.wr, hp.rd, hp.wr],
      contains_offset (by omega) (by omega)⟩ fun s₃ u₃ => ?_
  have hoA : addr (op s₀ + BitVec.ofNat 32 i) 0 = oA s₀ + BitVec.ofNat 64 i := ptr_addr (by omega)
  refine wp_store8 (r := .al) (a := oA s₀ + BitVec.ofNat 64 i)
    (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.esi, hoA])
    (by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr, hp.wr]; exact ⟨oR s₀, by simp, contains_offset (by omega) (by omega)⟩)
    fun s₄ u₄ => ?_
  refine wp_addi fun s₅ u₅ => ?_
  have e₅ : s₅.gpr .ecx = st s₀ + BitVec.ofNat 32 (pos + 1) := by
    rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), e₂, ofNat_add_one]
  have hb₅ : s₅.gpr .ebp = scr s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.ebp]
  have w₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  refine wp_store (a := addr (scr s₀) 528) (by rw [ea_at, hb₅]) (hp.scr_out w₅ (by omega)) fun s₆ u₆ => ?_
  refine wp_store (a := addr (scr s₀) 532) (by rw [ea_at, u₆.gpr, hb₅])
    (hp.scr_out (by rw [u₆.wr, w₅]) (by omega)) fun s₇ u₇ => ?_
  refine wp_addi fun s₈ u₈ => wp_subi fun s₉ u₉ z₉ => WP.block_nil ?_
  -- The memory.
  have hb : s.mem (stA s₀ + BitVec.ofNat 64 pos) = byteOf (iterF k (S₀ s₀)) pos := by
    rw [← hI.state, VG.Proof.Sha3.byteOf_stateAt _ _ (by omega)]
  have hm₄ : s₄.mem = s.mem.writeW (oA s₀ + BitVec.ofNat 64 i) (byteOf (iterF k (S₀ s₀)) pos) := by
    rw [u₄.mem, show Reg8.al.reg = Reg.eax from rfl, u₃.gpr, u₃.mem, u₂.mem, u₁.mem, byte_low, hb]
  have hm : s₉.mem = (s₄.mem.writeW (addr (scr s₀) 528) (st s₀ + BitVec.ofNat 32 (pos + 1))).writeW
      (addr (scr s₀) 532) (arg s₀ 1) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), d₂,
      u₆.mem, u₅.mem, e₅]
  have hfo : Frame [oR s₀] s.mem s₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_offset (by omega) (by omega))
  have hfc : Frame [scR s₀] s₄.mem s₉.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) fC)).writeW
      (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) fC)
  -- The registers.
  have g : ∀ r, r ∉ [Reg.ecx, .edx, .eax, .esi, .edi] → s₉.gpr r = s.gpr r := fun r hr => by
    have ⟨a, b, c', d, e⟩ : r ≠ .ecx ∧ r ≠ .edx ∧ r ≠ .eax ∧ r ≠ .esi ∧ r ≠ .edi := by simpa using hr
    rw [u₉.other r e, u₈.other r d, u₇.gpr, u₆.gpr, u₅.other r a, u₄.gpr, u₃.other r c', u₂.other r b,
      u₁.other r a]
  have h₉ : s₉.gpr .edi = BitVec.ofNat 32 (outn s₀ - (i + 1)) := by
    rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.edi,
      VG.Proof.Sha256.X86.Stream.ofNat_pred (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, by have := hI.hi; omega, by omega, ?_, ?_, by rw [g _ (by decide), hI.ebx],
    by rw [g _ (by decide), hI.ebp], by rw [g _ (by decide), hI.esp], ?_, h₉, ?_, ?_,
    hI.frame.trans ((hfo.mono (by simp)).trans (hfc.mono (by simp))), ?_, ?_, fun j hj => ?_⟩, ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.esi, ofNat_add_one]
  · rw [hm, sep _ _ 528 532 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [hm, Mem.readW_writeW_self32]
  · refine hI.saved.keep fun d h1 h2 => ?_
    rw [hm, sep _ _ d 532 (by omega) (by omega) (by omega), sep _ _ d 528 (by omega) (by omega) (by omega),
      hm₄, hp.scr_o _ (by omega) hi]
  · rw [Proof.Sha3.stateAt_congr fun j hj => hfc.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hj,
      Proof.Sha3.stateAt_congr fun j hj => hfo.bytes (R := stR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hI.state
  · rw [hfc.bytes (R := oR s₀) (by simpa using hp.o_scr) (by show outn s₀ ≤ 2 ^ 64; omega)
      (show j < outn s₀ by omega), hm₄]
    by_cases e : j = i
    · subst e
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr₀ hlt
      rw [writeW8_self, hI.hi, d, m]
    · rw [writeW8_other _ _ (Offset.add_ofNat_ne _ (by omega) (by omega) e)]
      exact hI.out j (by omega)
  · rw [z₉, u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.edi,
      VG.Proof.Sha256.X86.Stream.ofNat_pred (by omega), Nat.sub_sub,
      VG.Proof.Sha256.X86.Stream.ofNat_beq_zero (by omega)]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hi : i < outn s₀) :
    WP isa squeezeBody s fun s' => ∃ k' pos', Inv s₀ (i + 1) k' pos' s' ∧
      s'.zf = some (decide (outn s₀ - (i + 1) = 0)) := by
  have ⟨hr₀, _⟩ := hp.rt_pos
  unfold squeezeBody
  refine WP.seq (WP.mono (check_ok hp hI) fun s₁ ⟨hI₁, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ k' pos', Inv s₀ i k' pos' s ∧ pos' < rt s₀) ?_
    fun s₂ ⟨k', pos', hI₂, hlt⟩ => WP.mono (store_ok hp hI₂ hlt hi) fun s' h => ⟨k', pos' + 1, h⟩)
  unfold next
  refine WP.ite (decide (pos = rt s₀)) (by rw [show isa.eval .e s₁ = s₁.zf from rfl, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.mono (permute_ok hp hI₁) fun s' h => ⟨k + 1, 0, h, hr₀⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil ⟨k, pos, hI₁, by have := hI.pos_le; omega⟩

/-! ## The epilogue -/

theorem epilogue_eq : epilogue = [.mov .eax (.mem (at_ .ebp 528)), .alu .sub .eax (.reg .ebx),
    .mov .ecx (.reg .ebp), .mov .ebx (.mem (at_ .ecx 512)), .mov .esi (.mem (at_ .ecx 516)),
    .mov .edi (.mem (at_ .ecx 520)), .mov .ebp (.mem (at_ .ecx 524))] := rfl

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {k pos : Nat} {s : State} (hI : Inv s₀ (outn s₀) k pos s) :
    WP isa (.block epilogue) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Sha3.squeezeX86.post s₀ s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hpos : pos ≤ rt s₀ := hI.pos_le
  have hsv := hI.saved
  simp only [Saved, saved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hsv
  obtain ⟨v1, v2, v3, v4⟩ := hsv
  rw [epilogue_eq]
  refine wp_movm (a := addr (scr s₀) 528) (by rw [ea_at, hI.ebp]) (hp.scr_in hI.wr (by omega))
    fun s₁ u₁ => wp_sub fun s₂ u₂ _ => wp_mov fun s₃ u₃ => ?_
  have e₃ : s₃.gpr .ecx = scr s₀ := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.ebp]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have w₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr]
  refine wp_movm (a := addr (scr s₀) 512) (by rw [ea_at, e₃]) (hp.scr_in w₃ (by omega)) fun s₄ u₄ => ?_
  refine wp_movm (a := addr (scr s₀) 516) (by rw [ea_at, u₄.other _ (by decide), e₃])
    (hp.scr_in (by rw [u₄.wr, w₃]) (by omega)) fun s₅ u₅ => ?_
  refine wp_movm (a := addr (scr s₀) 520) (by rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), e₃])
    (hp.scr_in (by rw [u₅.wr, u₄.wr, w₃]) (by omega)) fun s₆ u₆ => ?_
  refine wp_movm (a := addr (scr s₀) 524) (by rw [ea_at, u₆.other _ (by decide), u₅.other _ (by decide),
    u₄.other _ (by decide), e₃]) (hp.scr_in (by rw [u₆.wr, u₅.wr, u₄.wr, w₃]) (by omega)) fun s₇ u₇ => ?_
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃]
  have hax : (s₇.gpr .eax).toNat = pos := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.ptr, hI.ebx, add_sub_self,
      VG.Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega)]
  refine WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_, by rw [hax]; exact hpos, fun d => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, m₃, v1]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, m₃, v2]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, m₃, v3]
    · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, m₃, v4]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.esp]
  · rw [m₇]
    exact hI.frame.readW (Region.contains_self _ _)
      (by simpa using ⟨hp.ret_st, hp.ret_o, hp.ret_scr, ret_stk (E := E s₀) (by have := hp.sp_fit; omega)
        hp.sp_lo⟩) (by decide)
  · show bytesAt s₇.mem (oA s₀) (outn s₀) = Spec.Sha3.squeezeFrom (rt s₀) (S₀ s₀) (pos₀ s₀) (outn s₀)
    rw [m₇]
    refine List.ext_getElem (by rw [length_squeezeFrom hr₀ (by omega)]; simp [bytesAt]) fun j h₁ _ => ?_
    have hj : j < outn s₀ := by simpa [bytesAt] using h₁
    rw [squeezeFrom_getElem hr₀ (by omega) _ hj]
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    exact hI.out j hj
  · show Spec.Sha3.squeezeFrom (rt s₀) (stateAt s₇.mem (stA s₀)) (s₇.gpr .eax).toNat d =
      Spec.Sha3.squeezeFrom (rt s₀) (S₀ s₀) (pos₀ s₀ + outn s₀) d
    rw [m₇, hI.state, hax, squeezeFrom_iterF hr₀ (by omega), ← hI.hi]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa squeeze s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.squeezeX86.post s₀ s' := by
  unfold squeeze
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ k pos, Inv s₀ (outn s₀) k pos s) ?_
    fun s₂ ⟨k, pos, hI₂⟩ => epilogue_ok hp hI₂)
  refine WP.ite (decide (outn s₀ = 0)) (by rw [show isa.eval .e s₁ = s₁.zf from rfl, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil ⟨0, pos₀ s₀, by rw [hb]; exact hI⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ i k pos, n = outn s₀ - i ∧ i < outn s₀ ∧ Inv s₀ i k pos s) ?_
      (outn s₀) s₁ ⟨0, 0, pos₀ s₀, by omega, by omega, hI⟩
    rintro n s ⟨i, k, pos, rfl, hi, hI⟩
    refine WP.mono (body_ok hp hI hi) fun s' ⟨k', pos', hI', hz'⟩ => ?_
    by_cases hl : outn s₀ - (i + 1) = 0
    · exact .inl ⟨by simp [eval, hz', hl], k', pos', by rwa [show i + 1 = outn s₀ by omega] at hI'⟩
    · exact .inr ⟨by simp [eval, hz', hl], _, by omega, i + 1, k', pos', rfl, by omega, hI'⟩

/-! ## Constant time -/

/-- The initial taint: `esp` is public, and points `4` bytes below the
arguments (writable region 3), which are public; the words of `state`,
`out` and `scratch` are the base addresses of regions 0, 1 and 2 (`out` of
unknown length). -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [200, 0, 640, 24], bases := [(.esp, 3, 4)],
    slots := [(3, 0, 24)], wbases := [(3, 0, 0), (3, 20, 2)], room := 12 }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hst := hp.st_fit; have hsc := hp.scr_fit; have ho := hp.o_fit
  have hs : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.sp_fit
  have hlo : 12 ≤ (s.gpr .esp).toNat := hp.sp_lo
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩ fun _ => ⟨hlo, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)))
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_o, hp.st_scr, hp.a_st.symm⟩, ⟨hp.o_scr, hp.a_o.symm⟩, hp.a_scr.symm, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · simp only [addr_toNat]; omega
    · simp only [addr_toNat]; omega
    · simp only [addr_toNat]; omega
    · show (addr (s.gpr .esp) 4).toNat + 24 ≤ 2 ^ 32
      rw [addr_eq (by omega), BitVec.toNat_add, addr_toNat, BitVec.toNat_ofNat]; omega
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'
    show addr (s.gpr .esp) 4 = (VG.X86.Taint.region s 3).base
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
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 20) 32) 0 = (scr s).setWidth 64
      rw [argWord_eq (n := 24) (by omega) (k := 20) (by omega)]
      simp [addr, scr, arg]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have e : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 τ₀.room, τ₀.room⟩ : Region) = stkR s :=
      (stk_eq hlo).symm
    rw [e]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.stk_st
    · exact hp.stk_o
    · exact hp.stk_scr
    · exact (arg_stk (n := 24) (by omega) hlo).symm

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.squeezeX86.pre s₁) (h₂ : Proof.Sha3.squeezeX86.pre s₂)
    (hpub : Proof.Sha3.squeezeX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [stR, oR, scR, argR, stA, oA, st, op, outn, scr, argAddr, ha 0 (by omega), ha 3 (by omega),
      ha 4 (by omega), ha 5 (by omega), hesp]
  · intro sl hsl
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl; decide
  · intro sl hsl k _ hk
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl
    simp only [Nat.zero_add] at hk
    simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp₁.wr, hp₂.wr]
    show s₁.mem (addr (s₁.gpr .esp) 4 + BitVec.ofNat 64 k) = s₂.mem (addr (s₂.gpr .esp) 4 + BitVec.ofNat 64 k)
    rw [argWord_eq (n := 24) (by have := hp₁.sp_fit; omega) hk,
      argWord_eq (n := 24) (by have := hp₂.sp_fit; omega) hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-- Memory holding the arguments `0x1000, 72, 0, 0x2000, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4008 then 72 else if a = 0x4011 then 0x20 else
  if a = 0x4019 then 0x30 else 0

/-- A state satisfying the precondition (with no output). -/
def sat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩, ⟨0x3000, 640⟩, ⟨0x4004, 24⟩]

theorem sat_pre : Proof.Sha3.squeezeX86.pre sat := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a1 : arg sat 1 = 72 := by decide
  have a2 : arg sat 2 = 0 := by decide
  have a3 : arg sat 3 = 0x2000 := by decide
  have a4 : arg sat 4 = 0 := by decide
  have a5 : arg sat 5 = 0x3000 := by decide
  have e : argAddr sat 0 = 0x4004 := by decide
  simp only [Proof.Sha3.squeezeX86, a0, a1, a2, a3, a4, a5, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩ <;>
  · exact Region.disjoint_of_sep (by decide)

theorem squeeze_verified : Verified X86.target squeeze Proof.Sha3.squeezeX86 := by
  refine ⟨fun s hs => correct (pre_of hs), ?_, ⟨sat, sat_pre⟩⟩
  exact VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide_weak VG.Proof.Sha3.X86.dropRC)

end VG.Proof.Sha3.X86.Stream.Squeeze
