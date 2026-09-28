import VerifiedGarbage.Proof.Sha3.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Range

/-!
# The SHA-3 sponge on x86-64: `absorb`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha3.X86_64.Stream.Absorb

open VG VG.X86_64 VG.Impl.Sha3.X86_64.Stream
open VG.Impl.Sha3.X86_64 (at_)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_movzx8 wp_store8 wp_store wp_xor wp_addi wp_subi
  wp_cmp wp_test wp_mov32i wp_nil ea_at contains_offset sub_offset off_disjoint toNat_ofNat_lt
  permuteAt_ok)
open VG.Proof.Sha3 (Rep rep_snoc xorByte stateAt_xorByte)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## Arithmetic -/

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

theorem xor_setWidth (x y : Byte) : (x.setWidth 64 ^^^ y.setWidth 64).setWidth 8 = x ^^^ y := by
  ext i hi
  simp

/-- A one-byte store. -/
theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    m.writeW a v x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h
    simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero, ite_true]
    ext i hi
    simp
  · have : ¬ (x - a).toNat < 8 / 8 := by bv_omega
    simp only [this, h, ite_false]

theorem bytesAt_succ (m : Mem) (p : Addr) (c : Nat) :
    bytesAt m p (c + 1) = bytesAt m p c ++ [m (p + BitVec.ofNat 64 c)] := by
  simp [bytesAt, List.range_succ]

theorem bytesAt_length (m : Mem) (p : Addr) (c : Nat) : (bytesAt m p c).length = c := by
  simp [bytesAt]

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev rt : Nat := (s₀.gpr .rsi).toNat
abbrev pos : Nat := (s₀.gpr .rdx).toNat
abbrev dp : Addr := s₀.gpr .rcx
abbrev len : Nat := (s₀.gpr .r8).toNat
abbrev scr : Addr := s₀.gpr .r9
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR : Region := ⟨scr s₀, 640⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- Where the call of `vg_keccak_f1600` stores its return address. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 8
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c

/-- The caller's callee-saved registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ k < 6, m.readW (scr s₀ + BitVec.ofNat 64 (512 + 8 * k)) 64 = s₀.gpr (saved.getD k (.rax, 0)).1

/-- The messages the initial state and position represent. -/
def Msg (msg : List Byte) : Prop :=
  stateAt s₀.mem (st s₀) = Rep (rt s₀) msg ∧ pos s₀ = msg.length % rt s₀

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀, scR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀)
  d_scr : (dR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem Pre.rt_pos {s₀ : State} (hp : Pre s₀) : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  have h := hp.rate
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt

theorem rsi_eq (s₀ : State) : s₀.gpr .rsi = BitVec.ofNat 64 (rt s₀) := by simp [rt]

/-- Writes to the state, the first 512 bytes of scratch and below the stack
keep the saved registers. -/
theorem Saved.frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [stR s₀, ⟨scr s₀, 512⟩, stkR s₀] m m') : Saved s₀ m' := by
  intro k hk
  rw [← h k hk]
  refine hf.readW (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left (sub_offset (by omega) (by omega))
  · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  · exact hp.stk_scr.symm.sub_left (sub_offset (by omega) (by omega))

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = st s₀
  r15 : s.gpr .r15 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r13 : s.gpr .r13 = dp s₀ + BitVec.ofNat 64 c
  r14 : s.gpr .r14 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  r12 : s.gpr .r12 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)
  repr : ∀ msg, Msg s₀ msg → stateAt s.mem (st s₀) = Rep (rt s₀) (msg ++ D s₀ c)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hg : ∀ r ∈ [Reg.rbx, .r15, .rsp, .rbp, .r13, .r14], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg _ (by simp)]; exact h.rbx
  r15 := by rw [hg _ (by simp)]; exact h.r15
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  rbp := by rw [hg _ (by simp)]; exact h.rbp
  r13 := by rw [hg _ (by simp)]; exact h.r13
  r14 := by rw [hg _ (by simp)]; exact h.r14
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- A call of the permutation keeps what holds throughout. -/
theorem Common.after_call {s₀ : State} (hp : Pre s₀) {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame [stR s₀, ⟨scr s₀, 512⟩, stkR s₀] s.mem s'.mem) : Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hcs _ (by decide)]; exact h.rbx
  r15 := by rw [hcs _ (by decide)]; exact h.r15
  rsp := by rw [hcs _ (by decide)]; exact h.rsp
  rbp := by rw [hcs _ (by decide)]; exact h.rbp
  r13 := by rw [hcs _ (by decide)]; exact h.r13
  r14 := by rw [hcs _ (by decide)]; exact h.r14
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  saved := h.saved.frame hp hf

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩) (len_lt s₀).le hi

/-! ## The prologue -/

theorem save_eq : save .r9 = (List.range 6).flatMap fun k =>
    [.store (at_ .r9 (512 + 8 * k)) ((saved.getD k (.rax, 0)).1)] := by decide

/-- During the saves. -/
def SaveInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    Frame [⟨scr s₀ + BitVec.ofNat 64 512, 48⟩] s₀.mem s.mem ∧
    ∀ j < k, s.mem.readW (scr s₀ + BitVec.ofNat 64 (512 + 8 * j)) 64 = s₀.gpr ((saved.getD j (.rax, 0)).1)

theorem saves_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block ((List.range 6).flatMap fun k =>
      [.store (at_ .r9 (512 + 8 * k)) ((saved.getD k (.rax, 0)).1)])) s₀ (SaveInv s₀ 6) := by
  refine wp_range_flatMap (M := isa) (SaveInv s₀) (fun k s hk ⟨hg, hrd, hwr, hf, hv⟩ => ?_) 6 le_rfl s₀
    ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  refine wp_store (a := scr s₀ + BitVec.ofNat 64 (512 + 8 * k)) (by rw [ea_at, hg])
    ⟨scR s₀, by simp [hwr, hp.wr], contains_offset (by omega) (by omega)⟩ fun s' g' m' r' w' => wp_nil ?_
  refine ⟨g'.trans hg, r'.trans hrd, w'.trans hwr, ?_, fun j hj => ?_⟩
  · rw [m']
    refine hf.writeW (List.mem_singleton_self _) _ ?_
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact contains_offset (by omega) (by omega)
  · rw [m', hg]
    by_cases e : j = k
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact hv j (by omega)
      · have := off_disjoint (scr s₀) (a := 512 + 8 * j) (n := 8) (b := 512 + 8 * k) (k := 8)
          (by omega) (by omega) (by omega)
        exact this.sep (Region.contains_self _ _) (Region.contains_self _ _)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save .r9 ++ [.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .r13 (.reg .rcx), .mov .r14 (.reg .r8), .mov .r15 (.reg .r9), .alu .test .r14 (.reg .r14)]))
      s₀ fun s => Inv s₀ 0 s ∧ s.zf = some (decide (len s₀ = 0)) := by
  rw [save_eq, WP.block_append_iff]
  refine WP.mono (saves_ok hp) fun s₁ ⟨g₁, rd₁, wr₁, f₁, v₁⟩ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => wp_test fun s₈ g₈ m₈ rd₈ wr₈ z₈ => wp_nil ?_
  have hm : s₈.mem = s₁.mem := by rw [m₈, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have hrd : s₈.rd = s₀.rd := by rw [rd₈, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have hwr : s₈.wr = s₀.wr := by rw [wr₈, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have hf : Frame [stR s₀, scR s₀, stkR s₀] s₀.mem s₁.mem :=
    f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, sub_offset (by omega) (by omega)⟩
  have h14 : s₈.gpr .r14 = s₀.gpr .r8 := by
    rw [g₈, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  have hl := len_lt s₀
  refine ⟨⟨⟨Nat.zero_le _, hrd, hwr, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm]; exact hf,
    fun k hk => by rw [hm]; exact v₁ k hk⟩, ?_, fun msg ⟨hs, _⟩ => ?_⟩, ?_⟩
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [g₈, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [h14, Nat.sub_zero]; simp [len]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₁, Nat.add_zero, Nat.mod_eq_of_lt hp.pos_lt]
    simp [pos]
  · rw [hm, show D s₀ 0 = [] by simp [bytesAt], List.append_nil, ← hs]
    exact Proof.Sha3.stateAt_congr fun i hi =>
      f₁.bytes (R := stR s₀) (by simpa using hp.st_scr.sub_right (sub_offset (by omega) (by omega)))
        (by simp) hi
  · rw [z₈, ← congrFun g₈ .r14, h14, BitVec.and_self]
    rw [show s₀.gpr .r8 = BitVec.ofNat 64 (len s₀) by simp [len], ofNat_beq_zero hl]

/-! ## One iteration -/

/-- The state after absorbing `c` bytes, then the byte at the position `j`
XORed in. -/
theorem body_block {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa (.block [.movzx8 .rax { base := .r13 }, .movzx8 .rcx stByte, .alu .xor .rax (.reg .rcx),
      .store8 stByte .rax, .alu .add .r13 (.imm 1), .alu .add .r12 (.imm 1),
      .alu .sub .r14 (.imm 1), .alu .cmp .r12 (.reg .rbp)]) s fun s' =>
      Common s₀ (c + 1) s' ∧ s'.gpr .r12 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 1) ∧
      s'.zf = some (decide ((pos s₀ + c) % rt s₀ + 1 = rt s₀)) ∧
      stateAt s'.mem (st s₀) = xorByte (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (s₀.mem (dp s₀ + BitVec.ofNat 64 c)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := len_lt s₀
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj ⊢
  have hr12 : s.gpr .r12 = BitVec.ofNat 64 j := by rw [hI.r12, hjd]
  have hrbx := hI.rbx
  have hin : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 c) 1 :=
    ⟨dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hst : ∀ t : State, t.gpr .rbx = st s₀ → t.gpr .r12 = BitVec.ofNat 64 j →
      t.ea stByte = st s₀ + BitVec.ofNat 64 j := fun t h1 h2 => by
    simp [State.ea, stByte, h1, h2]
  have hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 1 :=
    fun rs h => ⟨stR s₀, h, contains_offset (by omega) (by omega)⟩
  refine wp_movzx8 (d := .rax) (a := dp s₀ + BitVec.ofNat 64 c) (by simp [State.ea, hI.r13]) hin
    fun s₁ u₁ => ?_
  refine wp_movzx8 (d := .rcx) (a := st s₀ + BitVec.ofNat 64 j)
    (hst _ (by rw [u₁.other _ (by decide), hrbx]) (by rw [u₁.other _ (by decide), hr12]))
    (hsin _ (by simp [u₁.rd, u₁.wr, hI.rd, hI.wr, hp.wr])) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_store8 (r := .rax) (a := st s₀ + BitVec.ofNat 64 j)
    (hst _ (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hrbx])
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hr12]))
    (hsin _ (by simp [u₃.wr, u₂.wr, u₁.wr, hI.wr, hp.wr])) fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_addi fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_subi fun s₇ u₇ _ =>
    wp_cmp fun s₈ g₈ m₈ rd₈ wr₈ _ z₈ => wp_nil ?_
  -- The byte stored.
  have hv : (s₃.gpr .rax).setWidth 8 =
      s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem, xor_setWidth, hI.data hp hc]
  have hm₈ : s₈.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j)
      (s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j)) := by
    rw [m₈, u₇.mem, u₆.mem, u₅.mem, m₄, hv, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [stR s₀] s.mem s₈.mem := by
    rw [hm₈]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))
  have g : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r13 → r ≠ .r12 → r ≠ .r14 → s₈.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [g₈, u₇.other r h5, u₆.other r h4, u₅.other r h3, g₄, u₃.other r h1, u₂.other r h2,
        u₁.other r h1]
  have h12 : s₈.gpr .r12 = BitVec.ofNat 64 (j + 1) := by
    rw [g₈, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hr12, sx1, ofNat_succ]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h12, ?_, ?_⟩
  · rw [rd₈, u₇.rd, u₆.rd, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [wr₈, u₇.wr, u₆.wr, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide) (by decide), hrbx]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide) (by decide), hI.r15]
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide) (by decide), hI.rsp]
  · rw [g .rbp (by decide) (by decide) (by decide) (by decide) (by decide), hI.rbp]
  · rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hI.r13, sx1, ofNat_succ, BitVec.add_assoc]
  · rw [g₈, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hI.r14, sx1, ofNat_pred (by omega), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.frame hp (hf.mono (by simp))
  · rw [z₈, ← congrFun g₈ .r12, ← congrFun g₈ .rbp, h12, g .rbp (by decide) (by decide) (by decide) (by decide) (by decide), hI.rbp, rsi_eq,
      sub_beq (by omega) (by omega)]
  · refine stateAt_xorByte (by omega) ?_ fun i hi hij => ?_
    · rw [hm₈, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₈, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false fun e => hij (by bv_omega))]

/-- The rest of the body, from after the block. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State} (hI : Inv s₀ c s) :
    WP isa absorbBody s fun s' =>
      (isa.eval .ne s' = some false ∧ Inv s₀ (len s₀) s') ∨
      (isa.eval .ne s' = some true ∧ c + 1 < len s₀ ∧ Inv s₀ (c + 1) s') := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := len_lt s₀
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  unfold absorbBody
  refine WP.seq (WP.mono (body_block hp hc hI) fun s₁ ⟨hC, h12, hz, hst⟩ => ?_)
  -- The representation after absorbing the byte.
  have hlen : ∀ msg, Msg s₀ msg → (msg ++ D s₀ c).length % rt s₀ = (pos s₀ + c) % rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, bytesAt_length, hpm, Nat.mod_add_mod]
  have hrep : ∀ msg, Msg s₀ msg → Rep (rt s₀) (msg ++ D s₀ (c + 1)) =
      if (pos s₀ + c) % rt s₀ + 1 = rt s₀ then keccakF (stateAt s₁.mem (st s₀))
      else stateAt s₁.mem (st s₀) := fun msg hm => by
    rw [D, bytesAt_succ, ← List.append_assoc, rep_snoc hr₀ (by omega), hlen msg hm, hst,
      hI.repr msg hm]
  have hpc : (pos s₀ + (c + 1)) % rt s₀ = if (pos s₀ + c) % rt s₀ + 1 = rt s₀ then 0
      else (pos s₀ + c) % rt s₀ + 1 := by
    have e := Nat.div_add_mod (pos s₀ + c) (rt s₀)
    rw [show pos s₀ + (c + 1) = (pos s₀ + c) + 1 by omega]
    generalize (pos s₀ + c) % rt s₀ = j at e hj ⊢
    generalize (pos s₀ + c) / rt s₀ = q at e
    rw [← e]
    split
    · rw [Nat.add_assoc, ‹j + 1 = rt s₀›, ← Nat.mul_succ, Nat.mul_mod_right]
    · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  -- The final test.
  have tail : ∀ t : State, Inv s₀ (c + 1) t →
      WP isa (.block [.alu .test .r14 (.reg .r14)]) t fun s' =>
        (isa.eval .ne s' = some false ∧ Inv s₀ (len s₀) s') ∨
        (isa.eval .ne s' = some true ∧ c + 1 < len s₀ ∧ Inv s₀ (c + 1) s') := by
    intro t ht
    refine wp_test fun s' g' m' rd' wr' z' => wp_nil ?_
    have ht' : Inv s₀ (c + 1) s' :=
      { ht.toCommon.of_gpr (fun r _ => by rw [g']) m' rd' wr' with
        r12 := by rw [g']; exact ht.r12
        repr := by rw [m']; exact ht.repr }
    have hz : isa.eval .ne s' = some (!decide (len s₀ - (c + 1) = 0)) := by
      simp only [eval, z', ht.r14, BitVec.and_self, ofNat_beq_zero (show len s₀ - (c + 1) < 2 ^ 64 by omega),
        Option.map_some]
    by_cases he : c + 1 = len s₀
    · exact .inl ⟨by rw [hz]; simp [he], he ▸ ht'⟩
    · exact .inr ⟨by rw [hz]; simp; omega, by omega, ht'⟩
  refine WP.seq (WP.mono (Q := Inv s₀ (c + 1)) ?_ fun t ht => tail t ht)
  refine WP.ite (decide ((pos s₀ + c) % rt s₀ + 1 = rt s₀)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_mov32i fun s₂ u₂ => wp_nil ?_)
    have hC₂ := hC.of_gpr (fun r hr => u₂.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₂.mem u₂.rd u₂.wr
    have hsp := hC₂.rsp
    refine permuteAt_ok hC₂.rbx hC₂.r15 (hp.st_scr.sub_right (Region.sub_prefix (by omega)))
      (by rw [hsp]; exact hp.stk_st) (by rw [hsp]; exact hp.stk_scr.sub_right (Region.sub_prefix (by omega)))
      ?_ fun s₃ rd₃ wr₃ cs₃ f₃ e₃ => ?_
    · rw [hC₂.wr, hp.wr]
      intro a n ⟨r, hr, hcn⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, hcn⟩
      · exact ⟨scR s₀, by simp, by simp only [Region.Contains] at hcn ⊢; omega⟩
    · have f₃' : Frame [stR s₀, ⟨scr s₀, 512⟩, stkR s₀] s₂.mem s₃.mem := by
        have := f₃; rw [hsp] at this; exact this
      refine { hC₂.after_call hp rd₃ wr₃ cs₃ f₃' with r12 := ?_, repr := fun msg hm => ?_ }
      · rw [cs₃ _ (by decide), u₂.gpr, hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]; rfl
      · rw [e₃, u₂.mem, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
  · simp only [decide_eq_false_iff_not] at hb
    refine wp_nil { hC with r12 := ?_, repr := fun msg hm => ?_ }
    · rw [h12, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

/-! ## The epilogue -/

theorem restore_eq : restore = (List.range 6).flatMap fun k =>
    [.mov ((saved.getD k (.rax, 0)).1) (.mem (at_ .r15 (512 + 8 * k)))] := by decide

theorem saved_ne : ∀ j < 6, ∀ k < 6, j ≠ k → (saved.getD j (.rax, 0)).1 ≠ (saved.getD k (.rax, 0)).1 := by
  decide

theorem saved_ne' : ∀ k < 6, (saved.getD k (.rax, 0)).1 ≠ .rax ∧ (saved.getD k (.rax, 0)).1 ≠ .rsp ∧
    (k < 5 → (saved.getD k (.rax, 0)).1 ≠ .r15) := by
  decide

/-- During the restores. -/
def ResInv (s₀ s₁ : State) (k : Nat) (s : State) : Prop :=
  (k < 6 → s.gpr .r15 = scr s₀) ∧ s.gpr .rax = s₁.gpr .rax ∧ s.gpr .rsp = s₀.gpr .rsp ∧
    s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧
    ∀ j < k, s.gpr ((saved.getD j (.rax, 0)).1) = s₀.gpr ((saved.getD j (.rax, 0)).1)

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block (.mov .rax (.reg .r12) :: restore)) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Sha3.absorbX86_64.post s₀ s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  refine wp_mov fun s₁ u₁ => ?_
  rw [restore_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (ResInv s₀ s₁) (fun k s' hk ⟨r15, ax, sp, m, rd, wr, v⟩ => ?_)
    6 le_rfl s₁ ⟨fun _ => by rw [u₁.other _ (by decide), hI.r15], rfl, by rw [u₁.other _ (by decide), hI.rsp],
      rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩) fun s' ⟨_, ax, sp, m, _, _, v⟩ => ?_
  · refine wp_movm (a := scr s₀ + BitVec.ofNat 64 (512 + 8 * k)) (by rw [ea_at, r15 hk])
      ⟨scR s₀, by simp [rd, wr, u₁.rd, u₁.wr, hI.wr, hp.wr], contains_offset (by omega) (by omega)⟩
      fun s'' h => wp_nil ?_
    have ne := saved_ne' k hk
    refine ⟨fun hk' => by rw [h.other _ (Ne.symm (ne.2.2 (by omega))), r15 hk], by rw [h.other _ (Ne.symm ne.1), ax],
      by rw [h.other _ (Ne.symm ne.2.1), sp], by rw [h.mem, m], by rw [h.rd, rd], by rw [h.wr, wr],
      fun j hj => ?_⟩
    by_cases e : j = k
    · subst e; rw [h.gpr, m, u₁.mem]; exact hI.saved j hk
    · rw [h.other _ (saved_ne j (by omega) k hk e), v j (by omega)]
  · refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg hm hpm => ?_, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact v 0 (by omega)
      · exact v 1 (by omega)
      · exact sp
      · exact v 2 (by omega)
      · exact v 3 (by omega)
      · exact v 4 (by omega)
      · exact v 5 (by omega)
    · rw [m, u₁.mem]
      exact hI.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr, ret_stk s₀⟩)
        (by decide)
    · rw [Proof.Sha3.repr_iff, m, u₁.mem]
      exact hI.repr msg ⟨hm, hpm⟩
    · rw [ax, u₁.gpr, hI.r12, toNat_ofNat_lt (by have := Nat.mod_lt (pos s₀ + len s₀) hr₀; omega)]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa absorb s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.absorbX86_64.post s₀ s' := by
  unfold absorb
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.ite (decide (len s₀ = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact wp_nil (by rw [hb]; exact hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_ (len s₀) s₁
      ⟨0, rfl, by omega, hI⟩
    rintro n s ⟨c, rfl, hc, hI⟩
    refine WP.mono (body_ok hp hc hI) fun s' h => ?_
    rcases h with ⟨he, hI'⟩ | ⟨he, hc', hI'⟩
    · exact .inl ⟨he, hI'⟩
    · exact .inr ⟨he, len s₀ - (c + 1), by omega, c + 1, rfl, hc', hI'⟩

/-! ## Constant time -/

/-- The initial taint: the arguments and `rsp` are public, and `rdi` and `r9`
point at the writable regions. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], flags := false, lens := [200, 640],
    bases := [(.rdi, 0), (.r9, 1)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.absorbX86_64.pre s₁)
    (h₂ : Proof.Sha3.absorbX86_64.pre s₂) (hpub : Proof.Sha3.absorbX86_64.pub s₁ s₂) :
    X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hpub
  have wf : ∀ s, Proof.Sha3.absorbX86_64.pre s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, hd, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, hd], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p6]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 72 | .rcx => 0x2000 | .r9 => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩]

theorem absorb_verified : Verified X86_64.target absorb Proof.Sha3.absorbX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)
  · refine ⟨sat, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat] at h₁ h₂
      bv_omega

end VG.Proof.Sha3.X86_64.Stream.Absorb
