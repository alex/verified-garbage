import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Finish
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Consts
import VerifiedGarbage.Proof.ChaCha20.X86_64.Xor

/-!
# ChaCha20 keystream XOR on x86-64 with AVX2

Untrusted: everything here is checked by Lean. The loop over 512-byte chunks
(`Setup`, `Rounds`, `Finish`), the call of `vg_chacha20_xor` for the rest,
constant time and the calling convention.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20

/-! ## The contract -/

/-- `xorX86_64`, with 16 bytes of stack below the return address instead of
8: the call of `vg_chacha20_xor`, and its call of the block function, each
store a return address there. -/
def xorAvx2X86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, 320⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  post := xorX86_64.post
  pub := xorX86_64.pub

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev est : Addr := s₀.gpr .rdi
abbrev edp : Addr := s₀.gpr .rsi
abbrev eL : Nat := (s₀.gpr .rdx).toNat
abbrev ebp : Addr := s₀.gpr .rcx
abbrev edR : Region := ⟨edp s₀, eL s₀⟩
abbrev eret : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev estk : Region := below (s₀.gpr .rsp) 16
/-- The state, the data and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (est s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (edp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (S0 s₀) (eL s₀)
/-- The regions the code writes. -/
abbrev frR : List Region := [stR (est s₀), edR s₀, bufR (ebp s₀)]
end

theorem eL_lt (s₀ : State) : eL s₀ < 2 ^ 64 := (s₀.gpr .rdx).isLt

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = frR s₀
  st_d : (stR (est s₀)).Disjoint (edR s₀)
  st_b : (stR (est s₀)).Disjoint (bufR (ebp s₀))
  d_b : (edR s₀).Disjoint (bufR (ebp s₀))
  ret_st : (eret s₀).Disjoint (stR (est s₀))
  ret_d : (eret s₀).Disjoint (edR s₀)
  ret_b : (eret s₀).Disjoint (bufR (ebp s₀))
  stk_st : (estk s₀).Disjoint (stR (est s₀))
  stk_d : (estk s₀).Disjoint (edR s₀)
  stk_b : (estk s₀).Disjoint (bufR (ebp s₀))
  nowrap : (edp s₀).toNat + eL s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : xorAvx2X86_64.pre s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem APre.w_st {s₀ : State} (hp : APre s₀) : stR (est s₀) ∈ s₀.wr := by simp [hp.wr]
theorem APre.w_b {s₀ : State} (hp : APre s₀) : bufR (ebp s₀) ∈ s₀.wr := by simp [hp.wr]
theorem APre.w_d {s₀ : State} (hp : APre s₀) : edR s₀ ∈ s₀.wr := by simp [hp.wr]

/-- Before chunk `t` (the loop's invariant). -/
structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = est s₀
  rcx : s.gpr .rcx = ebp s₀
  rsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (512 * t)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 512 * t)
  le : 512 * t ≤ eL s₀
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (est s₀) = ctr (S0 s₀) (8 * t)
  data : ∀ k < eL s₀, s.mem (edp s₀ + BitVec.ofNat 64 k) =
    if k < 512 * t then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  consts : Consts s.mem (ebp s₀)
  frame : Frame (frR s₀) s₀.mem s.mem

/-! ## Counters and keystream -/

theorem ctr_ctr (S : CState) (a b : Nat) : ctr (ctr S a) b = ctr S (a + b) := by
  simp only [ctr, Vector.set_set, Vector.getElem_set_self, BitVec.ofNat_add, BitVec.add_assoc]

theorem ctr_add (S : CState) (j n : Nat) :
    (ctr S j).set 12 ((ctr S j)[12] + BitVec.ofNat 32 n) = ctr S (j + n) := by
  rw [← ctr_ctr]; rfl

/-- The keystream from block `8 t` on. -/
theorem ks_shift (S : CState) {L t k : Nat} (hk : k < L) (ht : 512 * t ≤ k) :
    (keystream S L).getD k 0 =
      (serialize (Spec.ChaCha20.block (ctr (ctr S (8 * t)) ((k - 512 * t) / 64)))).getD
        ((k - 512 * t) % 64) 0 := by
  rw [keystream_getD _ hk, ctr_ctr, show 8 * t + (k - 512 * t) / 64 = k / 64 by omega,
    show (k - 512 * t) % 64 = k % 64 by omega]

/-! ## The end of a chunk -/

set_option simprocs false in
theorem next_ok {s₀ : State} (hp : APre s₀) {t : Nat} (hge : 512 ≤ eL s₀ - 512 * t) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (512 * t))
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 512 * t)) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block next) s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (512 * (t + 1)) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 512 * (t + 1)) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      stateAt s'.mem (est s₀) = (stateAt s.mem (est s₀)).set 12 ((stateAt s.mem (est s₀))[12] + 8) ∧
      Frame [stR (est s₀)] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.cf = some (decide (eL s₀ - 512 * (t + 1) < 512)) := by
  have hL := eL_lt s₀
  have c₁ : (stR (est s₀)).Contains (Xor.off (est s₀) 48) 4 := contains_off (by omega) (by omega)
  have i₁ : InRegions (s.rd ++ s.wr) (Xor.off (est s₀) 48) 4 :=
    ⟨stR (est s₀), by simp [hrd, hwr, hp.rd, hp.wr], c₁⟩
  have o₁ : InRegions s.wr (Xor.off (est s₀) 48) 4 := ⟨stR (est s₀), by simp [hwr, hp.wr], c₁⟩
  simp only [Xor.off] at i₁ o₁
  apply WP.of_runBlock
  simp (config := {decide := true}) only [next, runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.Proof.ChaCha20.X86_64.ea_at, readSrc, readSrc32, execAlu, execAlu32, arithFlags,
    State.load32, State.store32, State.setReg, State.setReg32, State.setFlags, hrdi, i₁, o₁, ite_true,
    ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  have hv : s.mem.readW (est s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) 32 = (stateAt s.mem (est s₀))[12] := by
    simp [stateAt]
  have hfs : Frame [stR (est s₀)] s.mem (s.mem.writeW (Xor.off (est s₀) 48)
      ((stateAt s.mem (est s₀))[12] + 8)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have hrdx' : (s.gpr .rdx).toNat = eL s₀ - 512 * t := by rw [hrdx, toNat_ofNat_lt (by omega)]
  have se : BitVec.signExtend 64 (512 : BitVec 32) = 512 := by decide
  have e : (s.gpr .rdx - 512).toNat = eL s₀ - 512 * (t + 1) := by rw [hrdx]; bv_omega
  rw [hv, se]
  refine ⟨by rw [hrsi]; bv_omega, by rw [hrdx]; bv_omega, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃],
    Xor.stateAt_writeW_counter _ _ _, hfs, trivial, trivial, ?_⟩
  rw [e]; rfl

/-! ## The chunk of data -/

section
variable {s₀ : State} {t : Nat}

theorem win_sub (hw : 512 * t + 512 ≤ eL s₀) :
    Region.Sub (dR5 (edp s₀ + BitVec.ofNat 64 (512 * t))) (edR s₀) := by
  have hL := eL_lt s₀
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem dwin {ws : List Region} (hd : edR s₀ ∈ ws) (hw : 512 * t + 512 ≤ eL s₀) :
    DWin ws (edp s₀ + BitVec.ofNat 64 (512 * t)) := by
  have hL := eL_lt s₀
  intro off n h
  refine ⟨edR s₀, hd, ?_⟩
  simp only [Region.Contains]; bv_omega

theorem in_dR {k : Nat} (hk : k < eL s₀) : (edR s₀).Contains (edp s₀ + BitVec.ofNat 64 k) 1 :=
  Xor.contains_ofNat (by omega) (by have := eL_lt s₀; omega)

theorem out_win (hw : 512 * t + 512 ≤ eL s₀) {k : Nat} (hk : k < eL s₀)
    (ho : k < 512 * t ∨ 512 * t + 512 ≤ k) :
    ¬ (dR5 (edp s₀ + BitVec.ofNat 64 (512 * t))).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := eL_lt s₀
  simp only [Region.Contains]; bv_omega

end

theorem Consts.frame {m m' : Mem} {buf : Addr} (h : Consts m buf) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (hiR buf).Disjoint r) : Consts m' buf := by
  have e : ∀ d, 128 ≤ d → d + 32 ≤ 320 →
      m'.readW (buf + BitVec.ofNat 64 d) 256 = m.readW (buf + BitVec.ofNat 64 d) 256 :=
    fun d h₁ h₂ => hf.readW (hiR_contains buf h₁ h₂) hd (by decide)
  refine ⟨?_, ?_, ⟨?_, ?_⟩, incs_frame h.inc hf hd⟩
  · rw [e 128 (by omega) (by omega)]; exact h.lo16
  · rw [e 128 (by omega) (by omega)]; exact h.hi16
  · rw [e 160 (by omega) (by omega)]; exact h.m8.1
  · rw [e 160 (by omega) (by omega)]; exact h.m8.2

theorem plus_block (S : CState) (j : Nat) :
    plus (fun j => Nat.repeat Spec.ChaCha20.innerBlock 10 (ctr S j)) S j =
      Spec.ChaCha20.block (ctr S j) := rfl

/-! ## A chunk -/

theorem body_eq : body = .seq (.block setup) (.seq (rounds 10) (.block (finish ++ next))) := rfl

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax ∧ r ≠ .rsi ∧ r ≠ .rdx := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem body_ok {s₀ : State} (hp : APre s₀) {t : Nat} (hge : 512 ≤ eL s₀ - 512 * t) {s : State}
    (h : LInv s₀ t s) :
    WP isa body s fun s' =>
      LInv s₀ (t + 1) s' ∧ s'.cf = some (decide (eL s₀ - 512 * (t + 1) < 512)) := by
  have hL := eL_lt s₀
  have hw : 512 * t + 512 ≤ eL s₀ := by omega
  have hst : stR (est s₀) ∈ s.wr := by rw [h.wr]; exact hp.w_st
  have hb : bufR (ebp s₀) ∈ s.wr := by rw [h.wr]; exact hp.w_b
  have hd : edR s₀ ∈ s.wr := by rw [h.wr]; exact hp.w_d
  have sw := win_sub hw
  have dsd := hp.st_d.sub_right sw
  have dbd := hp.d_b.symm.sub_right sw
  have dss : (stR (est s₀)).Disjoint (slotsR (ebp s₀)) := hp.st_b.sub_right (slotsR_sub _)
  have hsl : ∀ r ∈ [slotsR (ebp s₀)], (hiR (ebp s₀)).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hiR_slots _
  rw [body_eq]
  refine WP.seq (WP.mono (setup_ok h.rdi h.rcx hst hb h.consts)
    fun s₁ ⟨hh, h15, g₁, rd₁, wr₁, y₁, y₂, m₁⟩ => ?_)
  have c₁ : Consts s₁.mem (ebp s₀) := by rw [m₁]; exact h.consts.w2 (by decide) y₁ y₂
  have F₁ : Frame [slotsR (ebp s₀)] s.mem s₁.mem := by
    rw [m₁]; exact W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)
  refine WP.seq (WP.mono (rounds_ok hh h15 (by rw [g₁]; exact h.rcx) (by rw [wr₁]; exact hb) c₁.m8 10)
    fun s₂ hr => ?_)
  have F₂ := F₁.trans hr.frame
  have g₂ : s₂.gpr = s.gpr := hr.gpr.trans g₁
  have wr₂ : s₂.wr = s.wr := hr.wr.trans wr₁
  refine WP.block_append (WP.mono (finish_ok hr.holds (st := est s₀) (by rw [g₂]; exact h.rdi)
    (by rw [g₂]; exact h.rcx) (by rw [g₂]; exact h.rsi) (by rw [wr₂]; exact hst)
    (by rw [wr₂]; exact hb) (dwin (by rw [wr₂]; exact hd) hw) (incs_frame c₁.inc hr.frame hsl)
    dsd hp.st_b dbd) fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  have F₃ : Frame [slotsR (ebp s₀), dR5 (edp s₀ + BitVec.ofNat 64 (512 * t))] s.mem s₃.mem :=
    (F₂.mono (by simp)).trans f₃
  have hS₂ : stateAt s₂.mem (est s₀) = stateAt s.mem (est s₀) :=
    Xor.stateAt_frame F₂ (by simpa using dss)
  have hS₃ : stateAt s₃.mem (est s₀) = stateAt s.mem (est s₀) :=
    Xor.stateAt_frame F₃ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dss
      · exact dsd)
  refine WP.mono (next_ok hp hge (by rw [g₃']; exact h.rdi) (by rw [g₃']; exact h.rsi)
    (by rw [g₃']; exact h.rdx) (by rw [rd₃, hr.rd, rd₁, h.rd]) (by rw [wr₃, wr₂, h.wr]))
    fun s₄ ⟨e₁, e₂, e₃, e₄, f₄, rd₄, wr₄, cf₄⟩ => ⟨?_, cf₄⟩
  have FA : Frame [slotsR (ebp s₀), dR5 (edp s₀ + BitVec.ofNat 64 (512 * t)), stR (est s₀)]
      s.mem s₄.mem := (F₃.mono (by simp)).trans (f₄.mono (by simp))
  have gk : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [e₃ r a b c, g₃']
  refine ⟨by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rdi,
    by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rcx, e₁, e₂, by omega,
    fun r hr => ?_, by rw [rd₄, rd₃, hr.rd, rd₁, h.rd], by rw [wr₄, wr₃, wr₂, h.wr], ?_,
    fun k hk => ?_, ?_, ?_⟩
  · obtain ⟨a, b, c⟩ := calleeSaved_ne hr
    rw [gk r a b c]; exact h.keep r hr
  · rw [e₄, hS₃, h.cnt, show 8 * (t + 1) = 8 * t + 8 by omega]
    exact ctr_add _ _ 8
  · have n_st : ¬ (stR (est s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
      hp.st_d _ hc (in_dR hk)
    have n_sl : ¬ (slotsR (ebp s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
      hp.d_b _ (in_dR hk) (slotsR_sub _ _ hc)
    by_cases hin : 512 * t ≤ k ∧ k < 512 * t + 512
    · have ea : edp s₀ + BitVec.ofNat 64 k =
          edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 (k - 512 * t) := by
        rw [add_ofNat, Nat.add_sub_cancel' hin.1]
      have x₃ := d₃ (k - 512 * t) (by omega)
      rw [← ea] at x₃
      rw [f₄ _ (by simpa using n_st), x₃, F₂ _ (by simpa using n_sl), h.data k hk,
        ite_eq_right (by omega : ¬ k < 512 * t), ite_eq_left (by omega : k < 512 * (t + 1)), hS₂,
        plus_block, h.cnt, ks_shift _ hk hin.1]
    · have n_w := out_win hw hk (by omega)
      rw [FA _ (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact n_sl
          · exact n_w
          · exact n_st), h.data k hk]
      by_cases hlt : k < 512 * t
      · rw [ite_eq_left hlt, ite_eq_left (by omega : k < 512 * (t + 1))]
      · rw [ite_eq_right hlt, ite_eq_right (by omega : ¬ k < 512 * (t + 1))]
  · refine c₁.frame (rs := [slotsR (ebp s₀), dR5 (edp s₀ + BitVec.ofNat 64 (512 * t)), stR (est s₀)])
      (((hr.frame.mono (by simp)).trans (f₃.mono (by simp))).trans (f₄.mono (by simp))) ?_
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact hiR_slots _
    · exact dbd.sub_left (hiR_sub _)
    · exact (hp.st_b.sub_right (hiR_sub _)).symm
  · refine h.frame.trans (FA.sub fun r hr' => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact ⟨bufR (ebp s₀), by simp, slotsR_sub _⟩
    · exact ⟨edR s₀, by simp, sw⟩
    · exact ⟨stR (est s₀), by simp, fun _ h => h⟩

/-! ## The prologue -/

set_option simprocs false in
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 512)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.cf = some (decide ((s.gpr .rdx).toNat < 512)) := by
  have se : BitVec.signExtend 64 (512 : BitVec 32) = 512 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  exact ⟨trivial, trivial, trivial, trivial, rfl⟩

theorem constPairs_le : ∀ p ∈ constPairs, p.1 + 8 ≤ 320 := by decide

theorem prologue_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (consts ++ ([.alu .cmp .rdx (.imm 512)] : List Instr))) s₀ fun s =>
      LInv s₀ 0 s ∧ s.cf = some (decide (eL s₀ < 512)) := by
  have hL := eL_lt s₀
  rw [consts_eq]
  refine WP.block_append (WP.mono (pairs_ok constPairs constPairs_le (s := s₀) rfl hp.w_b)
    fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => WP.mono (cmp_ok s₁) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  have F : Frame [bufR (ebp s₀)] s₀.mem s₂.mem := by
    rw [m₂, m₁]; exact storeAll_frame (List.mem_singleton_self _) _ constPairs_le _
  have gk : ∀ r, r ≠ .rax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, g₁ r hr]
  refine ⟨⟨gk _ (by decide), gk _ (by decide), by rw [gk _ (by decide)]; simp,
    by rw [gk _ (by decide)]; simp, by omega, fun r hr => gk r (calleeSaved_ne hr).1,
    by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, fun k hk => ?_, ?_, ?_⟩, ?_⟩
  · rw [Xor.stateAt_frame F (by simpa using hp.st_b), Nat.mul_zero, ctr_zero]
  · rw [F _ (by simpa using fun hc => hp.d_b _ (in_dR hk) hc)]
    simp
  · rw [m₂, m₁]; exact consts_mem _ _
  · exact F.mono (by simp)
  · rw [cf₂, g₁ _ (by decide)]

/-! ## The rest, by `vg_chacha20_xor` -/

theorem xor_keeps : ((instrs Impl.ChaCha20.X86_64.Xor.xor).all fun i => !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem xor_nosp : NoSp Impl.ChaCha20.X86_64.Xor.xor := by
  intro i hi
  simpa using List.all_eq_true.mp xor_keeps i hi

theorem xor_depth : Impl.ChaCha20.X86_64.Xor.xor.depth = 1 := by decide +kernel

/-- Byte `k` of data XORed with `ks`. -/
theorem bytes_of_bytesAt {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {k : Nat} (hk : k < n) :
    m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0 := by
  have e := congrArg (fun l => l[k]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    List.getElem?_zipWith, List.getElem?_eq_getElem (show k < ks.length by omega)] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < ks.length by omega),
    Option.getD_some]
  simpa using e

section
variable {s₀ : State} {t : Nat}

/-- The data left for `vg_chacha20_xor`. -/
abbrev tR (s₀ : State) (t : Nat) : Region := ⟨edp s₀ + BitVec.ofNat 64 (512 * t), eL s₀ - 512 * t⟩

theorem tail_sub (ht : 512 * t ≤ eL s₀) : Region.Sub (tR s₀ t) (edR s₀) := by
  have hL := eL_lt s₀
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem not_tail {k : Nat} (hk : k < 512 * t) (ht : 512 * t ≤ eL s₀) :
    ¬ (tR s₀ t).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := eL_lt s₀
  simp only [Region.Contains]; bv_omega

theorem stk_ret (s₀ : State) : Region.Sub ⟨s₀.gpr .rsp - 8, 8⟩ (estk s₀) := by
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem stk_stk (s₀ : State) : Region.Sub ⟨s₀.gpr .rsp - 8 - 8, 8⟩ (estk s₀) := by
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem ret_stk (s₀ : State) : (eret s₀).Disjoint (estk s₀) := by
  intro x h₁ h₂; simp only [Region.Contains] at *; bv_omega

end

theorem vz_ok (s : State) :
    WP isa (.block [.vop .vzeroupper]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left',
    VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr]
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem tail_ok {s₀ : State} (hp : APre s₀) {t : Nat} (hlt : eL s₀ - 512 * t < 512) {s : State}
    (h : LInv s₀ t s) :
    WP isa (.seq (.block [.vop .vzeroupper]) (.call "vg_chacha20_xor" Impl.ChaCha20.X86_64.Xor.xor)) s
      fun s' => (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  have hL := eL_lt s₀
  have hle := h.le
  refine WP.seq (WP.mono (vz_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
  have hsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [g₁]; exact h.keep .rsp (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  have hn : (BitVec.ofNat 64 (eL s₀ - 512 * t)).toNat = eL s₀ - 512 * t := toNat_ofNat_lt (by omega)
  have hwr : s₁.wr = frR s₀ := by rw [wr₁, h.wr, hp.wr]
  have hrd : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  refine WP.call (k := xorStack 8) Xor.xor_rsi xor_nosp (by rw [xor_depth]; decide)
    (rd := []) (wr := [stR (est s₀), tR s₀ t, bufR (ebp s₀)]) ?_ ?_ ?_ ?_
  · rw [xorStack_pre8]
    simp only [xorX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
      hne _ (by decide : Reg.rdx ≠ .rsp), hne _ (by decide : Reg.rcx ≠ .rsp), g₁, h.rdi, h.rsi,
      h.rdx, h.rcx, hsp, hn]
    have ts := tail_sub (s₀ := s₀) h.le
    exact ⟨trivial, trivial, hp.st_d.sub_right ts, hp.st_b, hp.d_b.sub_left ts,
      hp.stk_st.sub_left (stk_ret s₀), (hp.stk_d.sub_left (stk_ret s₀)).sub_right ts,
      hp.stk_b.sub_left (stk_ret s₀), hp.stk_st.sub_left (stk_stk s₀),
      (hp.stk_d.sub_left (stk_stk s₀)).sub_right ts, hp.stk_b.sub_left (stk_stk s₀),
      by have := hp.nowrap; bv_omega⟩
  · rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR (est s₀), by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨edR s₀, by simp, 512 * t, rfl, show 512 * t + (eL s₀ - 512 * t) ≤ eL s₀ by omega⟩
    · exact ⟨bufR (ebp s₀), by simp, 0, by simp, show 0 + 320 ≤ 320 by omega⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR (est s₀), by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨edR s₀, by simp, 512 * t, rfl, show 512 * t + (eL s₀ - 512 * t) ≤ eL s₀ by omega⟩
    · exact ⟨bufR (ebp s₀), by simp, 0, by simp, show 0 + 320 ≤ 320 by omega⟩
  · intro s₂ _ _ hcs hf _ ⟨s₃, hm₃, hg₃, hpost, hrsi₃⟩
    rw [xor_depth, hsp] at hf
    have ts := tail_sub (s₀ := s₀) h.le
    have hce : stateAt s₁.callEntry.mem (est s₀) = stateAt s₁.mem (est s₀) := by
      rw [State.callEntry_mem]
      exact Xor.stateAt_frame (rs := [estk s₀])
        ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
          rw [hsp]; exact below_call _ (by omega) (by omega)))
        (by simpa using hp.stk_st.symm)
    have Fce : Frame [estk s₀] s₁.mem s₁.callEntry.mem := by
      rw [State.callEntry_mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
        rw [hsp]; exact below_call _ (by omega) (by omega))
    simp only [xorX86_64, State.withRegions_gpr, State.withRegions_mem,
      hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
      hne _ (by decide : Reg.rdx ≠ .rsp), g₁, h.rdi, h.rsi, h.rdx, hce, hm₃, m₁, h.cnt] at hpost
    rw [hn] at hpost
    refine ⟨⟨⟨fun r hr => by rw [hcs r hr, g₁]; exact h.keep r hr, ?_⟩, ?_⟩, ?_⟩
    rotate_right
    · rw [← hg₃ .rsi (by decide), hrsi₃, State.withRegions_gpr, hne _ (by decide), g₁, h.rcx]
    · refine (hf.readW (r := eret s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
      · intro r hr
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hp.ret_st
        · exact hp.ret_d.sub_right ts
        · exact hp.ret_b
        · exact ret_stk s₀
      · rw [m₁]
        refine h.frame.readW (Region.contains_self _ _) ?_ (by decide)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.ret_st
        · exact hp.ret_d
        · exact hp.ret_b
    · refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
      have hk2 : k < eL s₀ := hk
      have n_st : ¬ (stR (est s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
        hp.st_d _ hc (in_dR hk)
      have n_b : ¬ (bufR (ebp s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
        hp.d_b _ (in_dR hk) hc
      have n_sk : ¬ (estk s₀).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
        hp.stk_d _ hc (in_dR hk)
      by_cases hk' : k < 512 * t
      · rw [hf _ (by
          intro r hr
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact n_st
          · exact not_tail hk' h.le
          · exact n_b
          · exact n_sk), m₁, h.data k hk, ite_eq_left hk']
      · have ea : edp s₀ + BitVec.ofNat 64 k =
            edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 (k - 512 * t) := by
          rw [add_ofNat, Nat.add_sub_cancel' (by omega)]
        have x := bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 512 * t) (by omega)
        rw [← ea, Fce _ (by simpa using n_sk), m₁, h.data k hk2, ite_eq_right hk',
          keystream_getD _ (by omega)] at x
        rw [x, ks_shift _ hk2 (t := t) (by omega)]

/-! ## The whole function -/

theorem xor_eq : Impl.ChaCha20.X86_64.Avx2.xor =
    .seq (.block (consts ++ ([.alu .cmp .rdx (.imm 512)] : List Instr)))
    (.seq (.ite .b (.block []) (.loop body .ae))
    (.seq (.block [.vop .vzeroupper]) (.call "vg_chacha20_xor" Impl.ChaCha20.X86_64.Xor.xor))) := rfl

theorem correct {s₀ : State} (hp : APre s₀) :
    WP isa Impl.ChaCha20.X86_64.Avx2.xor s₀ fun s' =>
      (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  rw [xor_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, hc⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ t, eL s₀ - 512 * t < 512 ∧ LInv s₀ t s) ?_
    fun s₂ ⟨t, ht, h₂⟩ => tail_ok hp ht h₂)
  refine WP.ite (decide (eL s₀ < 512)) (by simp [eval, hc]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil (M := isa) ⟨0, by omega, h₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s =>
      ∃ t, n = eL s₀ - 512 * t ∧ 512 ≤ eL s₀ - 512 * t ∧ LInv s₀ t s
    have hstep : ∀ n s, Inv n s → WP isa body s (fun s' =>
        (eval .ae s' = some false ∧ ∃ t, eL s₀ - 512 * t < 512 ∧ LInv s₀ t s') ∨
        (eval .ae s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨t, rfl, ht, hI⟩
      refine WP.mono (body_ok hp ht hI) fun s' ⟨h', hc'⟩ => ?_
      by_cases hl : eL s₀ - 512 * (t + 1) < 512
      · exact .inl ⟨by simp [eval, hc', hl], t + 1, hl, h'⟩
      · exact .inr ⟨by simp [eval, hc', hl], eL s₀ - 512 * (t + 1), by omega, t + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep (eL s₀ - 512 * 0) s₁ ⟨0, rfl, by omega, h₁⟩

/-! ## Constant time -/

/-- The public registers and what is known about memory on entry: the lengths
of `state` and `buf` (the data's varies) and the registers holding their bases. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false, lens := [64, 0, 320],
    bases := [(.rdi, 0, 0), (.rsi, 1, 0), (.rcx, 2, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : xorAvx2X86_64.pre s₁) (h₂ : xorAvx2X86_64.pre s₂)
    (hpub : xorAvx2X86_64.pub s₁ s₂) : X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpub
  have wf : ∀ s, xorAvx2X86_64.pre s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, d1, d2, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, d1, d2, d3], by simp [hw, (s.gpr .rdx).isLt.le]⟩,
      fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p2, p3, p4]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 0⟩, ⟨0x3000, 320⟩]

/-- `vg_chacha20_xor_avx2` returns with `rsi` pointing at `buf`, as
`vg_chacha20_xor` does, for a caller that recomputes pointers from it. -/
theorem xor_rsi (s : State) (hs : xorAvx2X86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Avx2.xor s t s' ∧ abiPreserved s s' ∧
      (xorAvx2X86_64.post s s' ∧ s'.gpr .rsi = s.gpr .rcx) := by
  obtain ⟨t, s', he, ⟨h, hpost⟩, hr⟩ := correct (APre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h, hpost, hr⟩

theorem xor_correct (s : State) (hs : xorAvx2X86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Avx2.xor s t s' ∧ abiPreserved s s' ∧
      xorAvx2X86_64.post s s' :=
  (xor_rsi s hs).imp fun _ ⟨s', he, ha, h, _⟩ => ⟨s', he, ha, h⟩

theorem xor_ct : ConstantTime isa xorAvx2X86_64.pre xorAvx2X86_64.pub
    Impl.ChaCha20.X86_64.Avx2.xor :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

theorem xor_verified :
    Verified X86_64.target Impl.ChaCha20.X86_64.Avx2.xor
      (Spec.ChaCha20.xorContract X86_64.abi 16) :=
  Verified.of_correct xor_correct xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, X86_64.abi, X86_64.argRegs,
      xorAvx2X86_64, Proof.ChaCha20.xorX86_64]
      [sat] using sat)

end VG.Proof.ChaCha20.X86_64.Avx2
