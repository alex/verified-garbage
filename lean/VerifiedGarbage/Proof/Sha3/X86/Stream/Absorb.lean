import VerifiedGarbage.Proof.Sha3.X86.Permute

/-!
# The SHA-3 sponge on x86 (32-bit): `absorb`

The structure of the x86-64 proof (`VG.Proof.Sha3.X86_64.Stream.Absorb`), with
`state` in `ebx`, `scratch` in `ebp`, `data` in `esi`, the bytes left in
`edi`, and `state + pos` and `rate` in the scratch space.
-/

namespace VG.Proof.Sha3.X86.Stream.Absorb

open VG VG.X86 VG.Impl.Sha3.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movm wp_movzx8 wp_store wp_store8 wp_add
  wp_addi wp_sub wp_subi wp_cmp wp_test contains_addr addr_toNat)
open VG.Proof.Sha3.X86 (permuteCall_ok reg32 wp_xorm)
open VG.Proof.Sha3 (Rep rep_snoc xorByte stateAt_xorByte bytesAt_succ bytesAt_length writeW8_apply
  rate_bounds contains_offset)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev rt : Nat := (arg s₀ 1).toNat
abbrev pos : Nat := (arg s₀ 2).toNat
abbrev dp : BitVec 32 := arg s₀ 3
abbrev len : Nat := (arg s₀ 4).toNat
abbrev scr : BitVec 32 := arg s₀ 5
abbrev stA : Addr := (st s₀).setWidth 64
abbrev dA : Addr := (dp s₀).setWidth 64
abbrev stR : Region := ⟨stA s₀, 200⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 640⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 12
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dA s₀) c

/-- The caller's callee-saved registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop := ∀ p ∈ saved, m.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1

/-- The messages the initial state and position represent. -/
def Msg (msg : List Byte) : Prop :=
  stateAt s₀.mem (stA s₀) = Rep (rt s₀) msg ∧ pos s₀ = msg.length % rt s₀

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀, scR s₀, argR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀)
  d_scr : (dR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_d : (argR s₀).Disjoint (dR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + 200 ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 640 ≤ 2 ^ 32
  sp_lo : 12 ≤ (E s₀).toNat
  sp_fit : (E s₀).toNat + 28 ≤ 2 ^ 32
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩ := h
  have e := stk_eq h18
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by show (below _ _).Disjoint _; rw [e]; exact h12,
    by show (below _ _).Disjoint _; rw [e]; exact h13, by show (below _ _).Disjoint _; rw [e]; exact h14,
    h15, h16, h17, h18, h19, h20, h21⟩

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 32 := (arg s₀ 4).isLt

theorem argR_eq (s₀ : State) : argR s₀ = ⟨addr (E s₀) 4, 24⟩ := rfl

theorem arg_eq (s₀ : State) (i : Nat) : s₀.mem.readW (addr (E s₀) (4 + 4 * i)) 32 = arg s₀ i := rfl

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem rt_pos : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  have := rate_bounds hp.rate; omega

theorem arg_in {s : State} (hw : s.wr = s₀.wr) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 28) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) d) 4 :=
  ⟨argR s₀, by simp [hw, hp.wr], by rw [argR_eq s₀]; exact arg_contains (by have := hp.sp_fit; omega) h₁ h₂⟩

/-- The argument words are never written. -/
theorem arg_keep {m : Mem} (hf : Frame [stR s₀, scR s₀, stkR s₀] s₀.mem m) {d : Nat} (h₁ : 4 ≤ d)
    (h₂ : d + 4 ≤ 28) : m.readW (addr (E s₀) d) 32 = s₀.mem.readW (addr (E s₀) d) 32 := by
  have fit : (E s₀).toNat + 4 + 24 ≤ 2 ^ 32 := by have := hp.sp_fit; omega
  have hs := arg_word fit h₁ h₂
  refine hf.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (argR_eq s₀ ▸ hp.a_st).sub_left hs
  · exact (argR_eq s₀ ▸ hp.a_scr).sub_left hs
  · exact (arg_stk fit hp.sp_lo).sub_left hs

theorem scr_out {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 640) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hw, hp.wr], contains_addr hd (by omega) hp.scr_fit⟩

theorem scr_in {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 640) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := hp.scr_out hw hd; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A write within the scratch space. -/
theorem frame_scr {rs : List Region} (hr : scR s₀ ∈ rs) {m : Mem} (hf : Frame rs s₀.mem m) {d : Nat}
    (hd : d + 4 ≤ 640) (v : BitVec 32) : Frame rs s₀.mem (m.writeW (addr (scr s₀) d) v) :=
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

/-- A word of the scratch space is unchanged by a write to the state. -/
theorem scr_st (m : Mem) {d : Nat} (hd : d + 4 ≤ 640) {j : Nat} (hj : j < 200) (v : Byte) :
    (m.writeW (stA s₀ + BitVec.ofNat 64 j) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
  Mem.readW_writeW_sep (hp.st_scr.symm.sep (contains_addr hd (by omega) hp.scr_fit)
    (contains_offset (by omega) (by omega))) (by decide)

end Pre

theorem Saved.keep {s₀ : State} {m m' : Mem} (hs : Saved s₀ m)
    (hk : ∀ d, 512 ≤ d → d + 4 ≤ 528 → m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32) :
    Saved s₀ m' := fun p hp' => by
  have ⟨h1, h2⟩ : 512 ≤ p.2 ∧ p.2 + 4 ≤ 528 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp
  rw [hk _ h1 h2]; exact hs p hp'

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = E s₀
  esi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c
  edi : s.gpr .edi = BitVec.ofNat 32 (len s₀ - c)
  rate : s.mem.readW (addr (scr s₀) rOff) 32 = arg s₀ 1
  frame : Frame [stR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  ptr : s.mem.readW (addr (scr s₀) pOff) 32 = st s₀ + BitVec.ofNat 32 ((pos s₀ + c) % rt s₀)
  repr : ∀ msg, Msg s₀ msg → stateAt s.mem (stA s₀) = Rep (rt s₀) (msg ++ D s₀ c)

theorem Common.of_flags {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s) (u : Fupd s s') :
    Common s₀ c s' where
  c_le := h.c_le
  rd := u.rd.trans h.rd
  wr := u.wr.trans h.wr
  ebx := by rw [u.gpr]; exact h.ebx
  ebp := by rw [u.gpr]; exact h.ebp
  esp := by rw [u.gpr]; exact h.esp
  esi := by rw [u.gpr]; exact h.esi
  edi := by rw [u.gpr]; exact h.edi
  rate := by rw [u.mem]; exact h.rate
  frame := by rw [u.mem]; exact h.frame
  saved := by rw [u.mem]; exact h.saved

/-- A call of the permutation keeps what holds throughout. -/
theorem Common.after_call {s₀ : State} (hp : Pre s₀) {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame [reg32 (st s₀) 200, reg32 (scr s₀) 512, stkR s₀] s.mem s'.mem) : Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hcs _ (by decide)]; exact h.ebx
  ebp := by rw [hcs _ (by decide)]; exact h.ebp
  esp := by rw [hcs _ (by decide)]; exact h.esp
  esi := by rw [hcs _ (by decide)]; exact h.esi
  edi := by rw [hcs _ (by decide)]; exact h.edi
  rate := by
    rw [hf.readW (Region.contains_self _ _) (hp.hi_sep (by decide) (by decide)) (by decide)]; exact h.rate
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  saved := h.saved.keep fun d h1 h2 => hf.readW (Region.contains_self _ _) (hp.hi_sep h1 (by omega))
    (by decide)

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dA s₀ + BitVec.ofNat 64 i) = s₀.mem (dA s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
    (by have := len_lt s₀; show len s₀ ≤ 2 ^ 64; omega) hi

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
    WP isa (.block setup) s₀ fun s => Inv s₀ 0 s ∧ s.zf = some (decide (len s₀ = 0)) := by
  have fC := hp.scr_fit
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
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
    rw [u₇.gpr, u₆.mem, hp.arg_keep (f₅.mono (by simp)) (by omega) (by omega)]; rfl
  have hpos : s₉.gpr .ecx = st s₀ + BitVec.ofNat 32 (pos s₀ % rt s₀) := by
    rw [u₉.gpr, u₈.gpr, u₈.other _ (by decide), hst, u₇.mem, u₆.mem, hp.arg_keep (f₅.mono (by simp)) (by omega) (by omega),
      Nat.mod_eq_of_lt hp.pos_lt, BitVec.add_comm]
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
    rw [u₁₁.gpr, hp.arg_keep (f₁₀.mono (by simp)) (by omega) (by omega)]; rfl
  have hdi : s₁₄.gpr .edi = arg s₀ 4 := by
    rw [u₁₄.gpr, u₁₃.mem, hp.arg_keep (f₁₂.mono (by simp)) (by omega) (by omega)]; rfl
  refine ⟨⟨⟨Nat.zero_le _, ?_, by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, hw₁₂], ?_, ?_, g .esp (by decide), ?_, ?_,
    ?_, by rw [hm]; exact f₁₂.mono (by simp), ?_⟩, ?_, fun msg ⟨hs, _⟩ => ?_⟩, ?_⟩
  · rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, r₅]
  · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), hst]
  · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.gpr, hb₉]
  · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.gpr, hp.arg_keep (f₁₂.mono (by simp)) (by omega) (by omega), BitVec.add_zero]
    rfl
  · rw [u₁₅.gpr, hdi, Nat.sub_zero]; simp [len]
  · rw [hm, hm₁₂, show rOff = 532 from rfl, Mem.readW_writeW_self32, hrate]
  · rw [hm, hm₁₂]
    refine sv₅.keep fun d h1 h2 => ?_
    rw [sep _ _ d 532 (by omega) (by omega) (by omega), u₁₀.mem, u₉.mem, m₈,
      sep _ _ d 528 (by omega) (by omega) (by omega)]
  · rw [hm, hm₁₂, show pOff = 528 from rfl, sep _ _ 528 532 (by omega) (by omega) (by omega), u₁₀.mem,
      Mem.readW_writeW_self32, Nat.add_zero]
    exact hpos
  · rw [show D s₀ 0 = [] by simp [bytesAt], List.append_nil, ← hs, hm]
    refine Proof.Sha3.stateAt_congr fun i hi => ?_
    exact f₁₂.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi
  · rw [z₁₅, hdi, BitVec.and_self]
    rw [show arg s₀ 4 = BitVec.ofNat 32 (len s₀) by simp [len], VG.Proof.Sha256.X86.Stream.ofNat_beq_zero (len_lt s₀)]

/-! ## One iteration -/

theorem body_eq : loadVars ++ absorbByte ++ storeVars ++ step ++ atEnd =
    [.mov .ecx (.mem (at_ .ebp 528)), .mov .edx (.mem (at_ .ebp 532)), .movzx8 .eax (at_ .esi 0),
      .alu .xor .eax (.mem (at_ .ecx 0)), .store8 (at_ .ecx 0) .al, .alu .add .ecx (.imm 1),
      .store (at_ .ebp 528) .ecx, .store (at_ .ebp 532) .edx, .alu .add .esi (.imm 1),
      .alu .sub .edi (.imm 1), .mov .eax (.reg .ecx), .alu .sub .eax (.reg .ebx),
      .alu .cmp .eax (.reg .edx)] := rfl

/-- The state after absorbing `c` bytes, then the byte at the position `j`
XORed in. -/
theorem body_block {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa (.block (loadVars ++ absorbByte ++ storeVars ++ step ++ atEnd)) s fun s' =>
      Common s₀ (c + 1) s' ∧
      s'.mem.readW (addr (scr s₀) pOff) 32 = st s₀ + BitVec.ofNat 32 ((pos s₀ + c) % rt s₀ + 1) ∧
      s'.zf = some (decide ((pos s₀ + c) % rt s₀ + 1 = rt s₀)) ∧
      stateAt s'.mem (stA s₀) = xorByte (stateAt s.mem (stA s₀)) ((pos s₀ + c) % rt s₀)
        (s₀.mem (dA s₀ + BitVec.ofNat 64 c)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := len_lt s₀
  have fS := hp.st_fit; have fC := hp.scr_fit; have fD := hp.d_fit
  have sep := fun (m : Mem) (v : BitVec 32) (d e : Nat) (hd : d + 4 ≤ 640) (he : e + 4 ≤ 640)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) => word_sep (b := scr s₀) (N := 640) fC hd he h m v
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  have hptr : s.mem.readW (addr (scr s₀) 528) 32 = st s₀ + BitVec.ofNat 32 ((pos s₀ + c) % rt s₀) :=
    hI.ptr
  generalize (pos s₀ + c) % rt s₀ = j at hj hptr ⊢
  rw [body_eq]
  refine wp_movm (a := addr (scr s₀) 528) (by rw [ea_at, hI.ebp]) (hp.scr_in hI.wr (by omega))
    fun s₁ u₁ => ?_
  refine wp_movm (a := addr (scr s₀) 532) (by rw [ea_at, u₁.other _ (by decide), hI.ebp])
    (hp.scr_in (by rw [u₁.wr, hI.wr]) (by omega)) fun s₂ u₂ => ?_
  have e₂ : s₂.gpr .ecx = st s₀ + BitVec.ofNat 32 j := by rw [u₂.other _ (by decide), u₁.gpr, hptr]
  have d₂ : s₂.gpr .edx = arg s₀ 1 := by rw [u₂.gpr, u₁.mem]; exact hI.rate
  have hdA : addr (dp s₀ + BitVec.ofNat 32 c) 0 = dA s₀ + BitVec.ofNat 64 c := ptr_addr (by omega)
  refine wp_movzx8 (a := dA s₀ + BitVec.ofNat 64 c)
    (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hI.esi, hdA])
    ⟨dR s₀, by simp [u₂.rd, u₁.rd, hI.rd, hp.rd], contains_offset (by omega) (by omega)⟩ fun s₃ u₃ => ?_
  have hsA : addr (st s₀ + BitVec.ofNat 32 j) 0 = stA s₀ + BitVec.ofNat 64 j := ptr_addr (by omega)
  have hsin : ∀ n, n ≤ 4 → InRegions s₀.wr (stA s₀ + BitVec.ofNat 64 j) n := fun n hn =>
    ⟨stR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩
  refine wp_xorm (b := .ecx) (B := st s₀ + BitVec.ofNat 32 j) (o := 0) (by rw [u₃.other _ (by decide), e₂])
    (by rw [hsA]; exact VG.Proof.Sha512.X86.mem_rd (by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr]; exact hsin 4 (by omega)))
    fun s₄ u₄ => ?_
  have e₄ : s₄.gpr .ecx = st s₀ + BitVec.ofNat 32 j := by rw [u₄.other _ (by decide), u₃.other _ (by decide), e₂]
  refine wp_store8 (r := .al) (a := stA s₀ + BitVec.ofNat 64 j) (by rw [ea_at, e₄, hsA])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]; exact hsin 1 (by omega)) fun s₅ u₅ => ?_
  refine wp_addi fun s₆ u₆ => ?_
  have e₆ : s₆.gpr .ecx = st s₀ + BitVec.ofNat 32 (j + 1) := by
    rw [u₆.gpr, u₅.gpr, e₄, ofNat_add_one]
  have hb₆ : s₆.gpr .ebp = scr s₀ := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hI.ebp]
  have w₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  refine wp_store (a := addr (scr s₀) 528) (by rw [ea_at, hb₆]) (hp.scr_out w₆ (by omega)) fun s₇ u₇ => ?_
  refine wp_store (a := addr (scr s₀) 532) (by rw [ea_at, u₇.gpr, hb₆])
    (hp.scr_out (by rw [u₇.wr, w₆]) (by omega)) fun s₈ u₈ => ?_
  refine wp_addi fun s₉ u₉ => wp_subi fun s₁₀ u₁₀ _ => wp_mov fun s₁₁ u₁₁ => wp_sub fun s₁₂ u₁₂ _ =>
    wp_cmp fun s₁₃ u₁₃ _ z₁₃ => WP.block_nil ?_
  -- The memory.
  have hv : (s₄.gpr Reg8.al.reg).setWidth 8 =
      s₀.mem (dA s₀ + BitVec.ofNat 64 c) ^^^ s.mem (stA s₀ + BitVec.ofNat 64 j) := by
    show (s₄.gpr .eax).setWidth 8 = _
    rw [u₄.gpr, u₃.gpr, u₃.mem, u₂.mem, u₁.mem, xor_low, hsA, low_byte, hI.data hp hc]
  have hm₁ : s₅.mem = s.mem.writeW (stA s₀ + BitVec.ofNat 64 j)
      (s₀.mem (dA s₀ + BitVec.ofNat 64 c) ^^^ s.mem (stA s₀ + BitVec.ofNat 64 j)) := by
    rw [u₅.mem, hv, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hm : s₁₃.mem = (s₅.mem.writeW (addr (scr s₀) 528) (st s₀ + BitVec.ofNat 32 (j + 1))).writeW
      (addr (scr s₀) 532) (arg s₀ 1) := by
    rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.gpr, u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), d₂, u₇.mem, u₆.mem, e₆]
  have hfs : Frame [stR s₀] s.mem s₅.mem := by
    rw [hm₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_offset (by omega) (by omega))
  have hfc : Frame [scR s₀] s₅.mem s₁₃.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) fC)).writeW
      (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) fC)
  have keep : ∀ d, 512 ≤ d → d + 4 ≤ 528 →
      s₁₃.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := fun d h1 h2 => by
    rw [hm, sep _ _ d 532 (by omega) (by omega) (by omega), sep _ _ d 528 (by omega) (by omega) (by omega),
      hm₁, hp.scr_st _ (by omega) (by omega)]
  -- The registers.
  have g : ∀ r, r ∉ [Reg.ecx, .edx, .eax, .esi, .edi] → s₁₃.gpr r = s.gpr r := fun r hr => by
    have ⟨a, b, c', d, e⟩ : r ≠ .ecx ∧ r ≠ .edx ∧ r ≠ .eax ∧ r ≠ .esi ∧ r ≠ .edi := by simpa using hr
    rw [u₁₃.gpr, u₁₂.other r c', u₁₁.other r c', u₁₀.other r e, u₉.other r d, u₈.gpr, u₇.gpr,
      u₆.other r a, u₅.gpr, u₄.other r c', u₃.other r c', u₂.other r b, u₁.other r a]
  have hc₁₀ : s₁₀.gpr .ecx = st s₀ + BitVec.ofNat 32 (j + 1) := by
    rw [u₁₀.other .ecx (by decide), u₉.other .ecx (by decide), u₈.gpr, u₇.gpr, e₆]
  have hb₁₁ : s₁₁.gpr .ebx = st s₀ := by
    rw [u₁₁.other .ebx (by decide), u₁₀.other .ebx (by decide), u₉.other .ebx (by decide), u₈.gpr, u₇.gpr,
      u₆.other .ebx (by decide), u₅.gpr, u₄.other .ebx (by decide), u₃.other .ebx (by decide),
      u₂.other .ebx (by decide), u₁.other .ebx (by decide), hI.ebx]
  have hax : s₁₂.gpr .eax = BitVec.ofNat 32 (j + 1) := by
    rw [u₁₂.gpr, u₁₁.gpr, hc₁₀, hb₁₁, add_sub_self]
  have hdx : s₁₂.gpr .edx = BitVec.ofNat 32 (rt s₀) := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), d₂]
    simp [rt]
  refine ⟨⟨by omega, ?_, ?_, by rw [g _ (by decide), hI.ebx], by rw [g _ (by decide), hI.ebp],
    by rw [g _ (by decide), hI.esp], ?_, ?_, ?_,
    hI.frame.trans ((hfs.mono (by simp)).trans (hfc.mono (by simp))), hI.saved.keep keep⟩, ?_, ?_, ?_⟩
  · rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, w₆]
  · rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.gpr,
      u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hI.esi, ofNat_add_one]
  · rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.gpr,
      u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hI.edi,
      VG.Proof.Sha256.X86.Stream.ofNat_pred (by omega), Nat.sub_sub]
  · rw [show rOff = 532 from rfl, hm, Mem.readW_writeW_self32]
  · rw [show pOff = 528 from rfl, hm, sep _ _ 528 532 (by omega) (by omega) (by omega),
      Mem.readW_writeW_self32]
  · rw [z₁₃, hax, hdx, VG.Proof.Sha256.X86.Stream.sub_beq (by omega) (by omega)]
  · rw [show stateAt s₁₃.mem (stA s₀) = stateAt s₅.mem (stA s₀) from
      Proof.Sha3.stateAt_congr fun i hi => hfc.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi]
    refine stateAt_xorByte (by omega) ?_ fun i hi hij => ?_
    · rw [hm₁, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₁, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (VG.Proof.Sha3.ne_of_lt200 hi (by omega) hij))]

/-- A store of the position keeps what holds throughout. -/
theorem Common.write_ptr {s₀ : State} (hp : Pre s₀) {c : Nat} {s s' : State} (h : Common s₀ c s)
    {v : BitVec 32} (u : Mupd s s' (s.mem.writeW (addr (scr s₀) 528) v)) : Common s₀ c s' where
  c_le := h.c_le
  rd := u.rd.trans h.rd
  wr := u.wr.trans h.wr
  ebx := by rw [u.gpr]; exact h.ebx
  ebp := by rw [u.gpr]; exact h.ebp
  esp := by rw [u.gpr]; exact h.esp
  esi := by rw [u.gpr]; exact h.esi
  edi := by rw [u.gpr]; exact h.edi
  rate := by
    rw [u.mem, show rOff = 532 from rfl, word_sep (N := 640) hp.scr_fit (by omega) (by omega) (by omega)]
    exact h.rate
  frame := by rw [u.mem]; exact hp.frame_scr (by simp) h.frame (by omega) _
  saved := h.saved.keep fun d h1 h2 => by
    rw [u.mem, word_sep (N := 640) hp.scr_fit (by omega) (by omega) (by omega)]

theorem pos_succ {r p c : Nat} (hr : 0 < r) :
    (p + (c + 1)) % r = if (p + c) % r + 1 = r then 0 else (p + c) % r + 1 := by
  have e := Nat.div_add_mod (p + c) r
  have hj := Nat.mod_lt (p + c) hr
  rw [show p + (c + 1) = (p + c) + 1 by omega]
  generalize (p + c) % r = j at e hj ⊢
  generalize (p + c) / r = q at e
  rw [← e]
  split
  · rw [Nat.add_assoc, ‹j + 1 = r›, ← Nat.mul_succ, Nat.mul_mod_right]
  · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State} (hI : Inv s₀ c s) :
    WP isa absorbBody s fun s' =>
      (isa.eval .ne s' = some false ∧ Inv s₀ (len s₀) s') ∨
      (isa.eval .ne s' = some true ∧ c + 1 < len s₀ ∧ Inv s₀ (c + 1) s') := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := len_lt s₀
  unfold absorbBody
  refine WP.seq (WP.mono (body_block hp hc hI) fun s₁ ⟨hC, hptr, hz, hst⟩ => ?_)
  have hlen : ∀ msg, Msg s₀ msg → (msg ++ D s₀ c).length % rt s₀ = (pos s₀ + c) % rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, bytesAt_length, hpm, Nat.mod_add_mod]
  have hrep : ∀ msg, Msg s₀ msg → Rep (rt s₀) (msg ++ D s₀ (c + 1)) =
      if (pos s₀ + c) % rt s₀ + 1 = rt s₀ then keccakF (stateAt s₁.mem (stA s₀))
      else stateAt s₁.mem (stA s₀) := fun msg hm => by
    rw [D, bytesAt_succ, ← List.append_assoc, rep_snoc hr₀ (by omega), hlen msg hm, hst,
      hI.repr msg hm]
  have hpc := pos_succ (p := pos s₀) (c := c) hr₀
  -- The final test.
  have tail : ∀ t : State, Inv s₀ (c + 1) t →
      WP isa (.block [.alu .test .edi (.reg .edi)]) t fun s' =>
        (isa.eval .ne s' = some false ∧ Inv s₀ (len s₀) s') ∨
        (isa.eval .ne s' = some true ∧ c + 1 < len s₀ ∧ Inv s₀ (c + 1) s') := by
    intro t ht
    refine wp_test fun s' u' z' => WP.block_nil ?_
    have ht' : Inv s₀ (c + 1) s' :=
      { ht.toCommon.of_flags u' with
        ptr := by rw [u'.mem]; exact ht.ptr
        repr := by rw [u'.mem]; exact ht.repr }
    have hz : isa.eval .ne s' = some (!decide (len s₀ - (c + 1) = 0)) := by
      simp only [eval, z', ht.edi, BitVec.and_self,
        VG.Proof.Sha256.X86.Stream.ofNat_beq_zero (show len s₀ - (c + 1) < 2 ^ 32 by omega), Option.map_some]
    by_cases he : c + 1 = len s₀
    · exact .inl ⟨by rw [hz]; simp [he], he ▸ ht'⟩
    · exact .inr ⟨by rw [hz]; simp; omega, by omega, ht'⟩
  refine WP.seq (WP.mono (Q := Inv s₀ (c + 1)) ?_ fun t ht => tail t ht)
  unfold next
  refine WP.ite (decide ((pos s₀ + c) % rt s₀ + 1 = rt s₀)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_store (a := addr (scr s₀) 528) (by rw [ea_at, hC.ebp]; rfl)
      (hp.scr_out hC.wr (by omega)) fun s₂ u₂ => WP.block_nil ?_)
    have hC₂ := hC.write_ptr hp u₂
    have hwr := hC₂.wr
    refine permuteCall_ok (st := .ebx) (scr := .ebp) (by decide) (by decide) hC₂.esp hC₂.ebx hC₂.ebp
      hp.sp_lo hp.st_fit (by have := hp.scr_fit; omega)
      (hp.st_scr.sub_right (Region.sub_prefix (by omega))) hp.stk_st
      (hp.stk_scr.sub_right (Region.sub_prefix (by omega))) (by rw [hwr, hp.wr]; simp)
      (by rw [hwr, hp.wr]; simp) fun s₃ rd₃ wr₃ cs₃ f₃ e₃ => ?_
    refine { hC₂.after_call hp rd₃ wr₃ cs₃ f₃ with ptr := ?_, repr := fun msg hm => ?_ }
    · rw [show pOff = 528 from rfl, f₃.readW (r := ⟨addr (scr s₀) 528, 4⟩) (Region.contains_self _ _)
        (hp.hi_sep (d := 528) (by omega) (by omega)) (by decide), u₂.mem, Mem.readW_writeW_self32, hC.ebx,
        hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]
      simp
    · rw [e₃, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
      refine congrArg keccakF (Proof.Sha3.stateAt_congr fun i hi => ?_)
      have hf : Frame [scR s₀] s₁.mem s₂.mem := by
        rw [u₂.mem]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (contains_addr (by omega) (by omega) hp.scr_fit)
      exact hf.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil { hC with ptr := ?_, repr := fun msg hm => ?_ }
    · rw [hptr, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

/-! ## The epilogue -/

theorem epilogue_eq : epilogue = [.mov .eax (.mem (at_ .ebp 528)), .alu .sub .eax (.reg .ebx),
    .mov .ecx (.reg .ebp), .mov .ebx (.mem (at_ .ecx 512)), .mov .esi (.mem (at_ .ecx 516)),
    .mov .edi (.mem (at_ .ecx 520)), .mov .ebp (.mem (at_ .ecx 524))] := rfl

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Sha3.absorbX86.post s₀ s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
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
    u₄.other _ (by decide), e₃]) (hp.scr_in (by rw [u₆.wr, u₅.wr, u₄.wr, w₃]) (by omega)) fun s₇ u₇ =>
    WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, fun msg hm hpm => ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, m₃, v1]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, m₃, v2]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, m₃, v3]
    · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, m₃, v4]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.esp]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃]
    exact hI.frame.readW (Region.contains_self _ _)
      (by simpa using ⟨hp.ret_st, hp.ret_scr, ret_stk (E := E s₀) (by have := hp.sp_fit; omega) hp.sp_lo⟩)
      (by decide)
  · rw [Proof.Sha3.repr_iff, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃]
    exact hI.repr msg ⟨hm, hpm⟩
  · have hptr : s.mem.readW (addr (scr s₀) 528) 32 = st s₀ + BitVec.ofNat 32 ((pos s₀ + len s₀) % rt s₀) :=
      hI.ptr
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hptr, hI.ebx, add_sub_self,
      VG.Proof.Sha256.X86.Stream.toNat_ofNat_lt (by have := Nat.mod_lt (pos s₀ + len s₀) hr₀; omega)]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa absorb s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.absorbX86.post s₀ s' := by
  unfold absorb
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.ite (decide (len s₀ = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (by rw [hb]; exact hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_ (len s₀) s₁
      ⟨0, rfl, by omega, hI⟩
    rintro n s ⟨c, rfl, hc, hI⟩
    refine WP.mono (body_ok hp hc hI) fun s' h => ?_
    rcases h with ⟨he, hI'⟩ | ⟨he, hc', hI'⟩
    · exact .inl ⟨he, hI'⟩
    · exact .inr ⟨he, len s₀ - (c + 1), by omega, c + 1, rfl, hc', hI'⟩

/-! ## Constant time -/

/-- The initial taint: `esp` is public, and points `4` bytes below the
arguments (writable region 2), which are public; the words of `state` and
`scratch` are the base addresses of regions 0 and 1. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [200, 640, 24], bases := [(.esp, 2, 4)],
    slots := [(2, 0, 24)], wbases := [(2, 0, 0), (2, 20, 1)], room := 12 }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hst := hp.st_fit; have hsc := hp.scr_fit
  have hs : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.sp_fit
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
    · show (addr (s.gpr .esp) 4).toNat + 24 ≤ 2 ^ 32
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
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 20) 32) 0 = (scr s).setWidth 64
      rw [argWord_eq (n := 24) (by omega) (k := 20) (by omega)]
      simp [addr, scr, arg]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have e : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 τ₀.room, τ₀.room⟩ : Region) = stkR s :=
      (stk_eq hlo).symm
    rw [e]
    rintro r (rfl | rfl | rfl)
    · exact hp.stk_st
    · exact hp.stk_scr
    · exact (arg_stk (n := 24) (by omega) hlo).symm

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.absorbX86.pre s₁) (h₂ : Proof.Sha3.absorbX86.pre s₂)
    (hpub : Proof.Sha3.absorbX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [stR, scR, argR, stA, st, scr, argAddr, ha 0 (by omega), ha 5 (by omega), hesp]
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

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩, ⟨0x4004, 24⟩]

theorem sat_pre : Proof.Sha3.absorbX86.pre sat := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a1 : arg sat 1 = 72 := by decide
  have a2 : arg sat 2 = 0 := by decide
  have a3 : arg sat 3 = 0x2000 := by decide
  have a4 : arg sat 4 = 0 := by decide
  have a5 : arg sat 5 = 0x3000 := by decide
  have e : argAddr sat 0 = 0x4004 := by decide
  simp only [Proof.Sha3.absorbX86, a0, a1, a2, a3, a4, a5, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩ <;>
  · exact Region.disjoint_of_sep (by decide)

theorem absorb_verified : Verified X86.target absorb Proof.Sha3.absorbX86 := by
  refine ⟨fun s hs => correct (pre_of hs), ?_, ⟨sat, sat_pre⟩⟩
  exact VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide_weak VG.Proof.Sha3.X86.dropRC)

end VG.Proof.Sha3.X86.Stream.Absorb
