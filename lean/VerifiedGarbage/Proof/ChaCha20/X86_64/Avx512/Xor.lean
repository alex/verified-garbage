import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Finish
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor

/-!
# ChaCha20 keystream XOR on x86-64 with AVX-512

Untrusted: everything here is checked by Lean. The loop over 1024-byte chunks
(`Setup`, `Rounds`, `Finish`), the call of `vg_chacha20_xor` for the rest,
constant time and the calling convention. The contract is that of
`vg_chacha20_xor_avx2` (`Avx2.xorAvx2X86_64`): 16 bytes of stack below the
return address, for the call of `vg_chacha20_xor` and its call of the block
function.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (APre est edp eL ebp edR eret estk S0 D0 KS frR eL_lt
  xorAvx2X86_64 add_ofNat in_dR)

/-! ## The loop invariant -/

/-- Before chunk `t`. -/
structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = est s₀
  rcx : s.gpr .rcx = ebp s₀
  rsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 1024 * t)
  le : 1024 * t ≤ eL s₀
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (est s₀) = ctr (S0 s₀) (16 * t)
  data : ∀ k < eL s₀, s.mem (edp s₀ + BitVec.ofNat 64 k) =
    if k < 1024 * t then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  incs : Incs s.mem (ebp s₀)
  frame : Frame (frR s₀) s₀.mem s.mem

/-- The keystream from block `16 t` on. -/
theorem ks_shift (S : CState) {L t k : Nat} (hk : k < L) (ht : 1024 * t ≤ k) :
    (keystream S L).getD k 0 =
      (serialize (Spec.ChaCha20.block (ctr (ctr S (16 * t)) ((k - 1024 * t) / 64)))).getD
        ((k - 1024 * t) % 64) 0 := by
  rw [keystream_getD _ hk, Avx2.ctr_ctr, show 16 * t + (k - 1024 * t) / 64 = k / 64 by omega,
    show (k - 1024 * t) % 64 = k % 64 by omega]

/-! ## The end of a chunk -/

set_option simprocs false in
theorem next_ok {s₀ : State} (hp : APre s₀) {t : Nat} (hge : 1024 ≤ eL s₀ - 1024 * t) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t))
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 1024 * t)) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block next) s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * (t + 1)) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 1024 * (t + 1)) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      stateAt s'.mem (est s₀) = (stateAt s.mem (est s₀)).set 12 ((stateAt s.mem (est s₀))[12] + 16) ∧
      Frame [Avx2.stR (est s₀)] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.cf = some (decide (eL s₀ - 1024 * (t + 1) < 1024)) := by
  have hL := eL_lt s₀
  have c₁ : (Avx2.stR (est s₀)).Contains (Xor.off (est s₀) 48) 4 := contains_off (by omega) (by omega)
  have i₁ : InRegions (s.rd ++ s.wr) (Xor.off (est s₀) 48) 4 :=
    ⟨Avx2.stR (est s₀), by simp [hrd, hwr, hp.rd, hp.wr], c₁⟩
  have o₁ : InRegions s.wr (Xor.off (est s₀) 48) 4 := ⟨Avx2.stR (est s₀), by simp [hwr, hp.wr], c₁⟩
  simp only [Xor.off] at i₁ o₁
  apply WP.of_runBlock
  simp (config := {decide := true}) only [next, runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.Proof.ChaCha20.X86_64.ea_at, readSrc, readSrc32, execAlu, execAlu32, arithFlags,
    State.load32, State.store32, State.setReg, State.setReg32, State.setFlags, hrdi, i₁, o₁, ite_true,
    ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  have hv : s.mem.readW (est s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) 32 = (stateAt s.mem (est s₀))[12] := by
    simp [stateAt]
  have hfs : Frame [Avx2.stR (est s₀)] s.mem (s.mem.writeW (Xor.off (est s₀) 48)
      ((stateAt s.mem (est s₀))[12] + 16)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have se : BitVec.signExtend 64 (1024 : BitVec 32) = 1024 := by decide
  have e : (s.gpr .rdx - 1024).toNat = eL s₀ - 1024 * (t + 1) := by rw [hrdx]; bv_omega
  rw [hv, se]
  refine ⟨by rw [hrsi]; bv_omega, by rw [hrdx]; bv_omega, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃],
    Xor.stateAt_writeW_counter _ _ _, hfs, trivial, trivial, ?_⟩
  rw [e]; rfl

/-! ## The chunk of data -/

section
variable {s₀ : State} {t : Nat}

/-- The 1024 bytes of chunk `t`. -/
abbrev wR (s₀ : State) (t : Nat) : Region := ⟨edp s₀ + BitVec.ofNat 64 (1024 * t), 1024⟩

/-- The counter increments in `buf`. -/
abbrev incR (s₀ : State) : Region := ⟨ebp s₀ + BitVec.ofNat 64 128, 64⟩

/-- The saved registers in `buf`. -/
abbrev saveR (s₀ : State) : Region := ⟨ebp s₀, 128⟩

theorem win_sub (hw : 1024 * t + 1024 ≤ eL s₀) : Region.Sub (wR s₀ t) (edR s₀) := by
  have hL := eL_lt s₀
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem out_win (hw : 1024 * t + 1024 ≤ eL s₀) {k : Nat} (hk : k < eL s₀)
    (ho : k < 1024 * t ∨ 1024 * t + 1024 ≤ k) :
    ¬ (wR s₀ t).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := eL_lt s₀
  simp only [Region.Contains]; bv_omega

theorem save_sub (s₀ : State) : Region.Sub (saveR s₀) (Avx2.bufR (ebp s₀)) := Region.sub_prefix (by omega)

theorem inc_sub (s₀ : State) : Region.Sub (incR s₀) (Avx2.bufR (ebp s₀)) := by
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem inc_save (s₀ : State) : (incR s₀).Disjoint (saveR s₀) := by
  intro x h₁ h₂; simp only [Region.Contains] at *; bv_omega

end

/-- Where a chunk runs: the regions of `Sym`, from the loop's. -/
theorem ctx_of {s₀ : State} (hp : APre s₀) {t : Nat} (hw : 1024 * t + 1024 ≤ eL s₀) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hrcx : s.gpr .rcx = ebp s₀)
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t)) (hwr : s.wr = s₀.wr) : Ctx s := by
  have hL := eL_lt s₀
  have r0 : regn s 0 = Avx2.stR (est s₀) := by simp only [regn, baseR, bsize, hrdi]
  have r1 : regn s 1 = Avx2.bufR (ebp s₀) := by simp only [regn, baseR, bsize, hrcx]
  have r2 : regn s 2 = wR s₀ t := by simp only [regn, baseR, bsize, hrsi]
  refine ⟨fun b i n hb h => ?_, fun b b' hb hb' ne => ?_⟩
  · rw [hwr, hp.wr]
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;> simp only [bsize] at h
    · rw [r0]
      exact ⟨Avx2.stR (est s₀), by simp, by
        simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega⟩
    · rw [r1]
      exact ⟨Avx2.bufR (ebp s₀), by simp, by
        simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega⟩
    · rw [r2]
      exact ⟨edR s₀, by simp, by simp only [Region.Contains]; bv_omega⟩
  · have d01 := hp.st_b
    have d02 := hp.st_d.sub_right (win_sub hw)
    have d12 := hp.d_b.symm.sub_right (win_sub hw)
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      rcases (by omega : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl <;>
      simp only [r0, r1, r2] <;>
      first | exact absurd rfl ne | assumption | exact d01.symm | exact d02.symm | exact d12.symm

theorem incs_frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : Incs m (ebp s₀))
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (incR s₀).Disjoint r) : Incs m' (ebp s₀) := by
  intro j hj
  rw [← h j hj]
  refine hf.readW (r := incR s₀) ?_ hd (by decide)
  simp only [Region.Contains]; bv_omega

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax ∧ r ≠ .rsi ∧ r ≠ .rdx :=
  Avx2.calleeSaved_ne hr

theorem body_eq : body = .seq (.block setup) (.seq (rounds 10) (.block (finish ++ next))) := rfl

theorem body_ok {s₀ : State} (hp : APre s₀) {t : Nat} (hge : 1024 ≤ eL s₀ - 1024 * t) {s : State}
    (h : LInv s₀ t s) :
    WP isa body s fun s' =>
      LInv s₀ (t + 1) s' ∧ s'.cf = some (decide (eL s₀ - 1024 * (t + 1) < 1024)) := by
  have hL := eL_lt s₀
  have hw : 1024 * t + 1024 ≤ eL s₀ := by omega
  have sw := win_sub hw
  have dsd := hp.st_d.sub_right sw
  have dbd := hp.d_b.symm.sub_right sw
  have hc : Ctx s := ctx_of hp hw h.rdi h.rcx h.rsi h.wr
  have hi : Incs s.mem (s.gpr .rcx) := by rw [h.rcx]; exact h.incs
  rw [body_eq]
  refine WP.seq (WP.mono (setup_ok hc hi) fun s₁ ⟨hz₁, m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds_ok hz₁ 10) fun s₂ ⟨hz₂, sm₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := sm₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := sm₂.mem.trans m₁
  have rd₂ : s₂.rd = s.rd := sm₂.rd.trans rd₁
  have wr₂ : s₂.wr = s.wr := sm₂.wr.trans wr₁
  have hc₂ : Ctx s₂ := ctx_of hp hw (by rw [g₂]; exact h.rdi) (by rw [g₂]; exact h.rcx)
    (by rw [g₂]; exact h.rsi) (by rw [wr₂]; exact h.wr)
  have hi₂ : Incs s₂.mem (s₂.gpr .rcx) := by rw [m₂, g₂]; exact hi
  refine WP.block_append (WP.mono (finish_ok hc₂ hi₂ hz₂) fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have ws : wregs s₂ = [saveR s₀, wR s₀ t] := by simp only [wregs, g₂, h.rcx, h.rsi]
  rw [ws, m₂] at f₃
  simp only [g₂, m₂, h.rsi, h.rdi] at d₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  refine WP.mono (next_ok hp hge (by rw [g₃']; exact h.rdi) (by rw [g₃']; exact h.rsi)
    (by rw [g₃']; exact h.rdx) (by rw [rd₃, rd₂, h.rd]) (by rw [wr₃, wr₂, h.wr]))
    fun s₄ ⟨e₁, e₂, e₃, e₄, f₄, rd₄, wr₄, cf₄⟩ => ⟨?_, cf₄⟩
  have dss : (Avx2.stR (est s₀)).Disjoint (saveR s₀) := hp.st_b.sub_right (save_sub _)
  have FA : Frame [saveR s₀, wR s₀ t, Avx2.stR (est s₀)] s.mem s₄.mem :=
    (f₃.mono (by simp)).trans (f₄.mono (by simp))
  have hS₃ : stateAt s₃.mem (est s₀) = stateAt s.mem (est s₀) :=
    Xor.stateAt_frame f₃ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dss
      · exact dsd)
  have gk : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [e₃ r a b c, g₃']
  refine ⟨by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rdi,
    by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rcx, e₁, e₂, by omega,
    fun r hr => ?_, by rw [rd₄, rd₃, rd₂, h.rd], by rw [wr₄, wr₃, wr₂, h.wr], ?_,
    fun k hk => ?_, ?_, ?_⟩
  · obtain ⟨a, b, c⟩ := calleeSaved_ne hr
    rw [gk r a b c]; exact h.keep r hr
  · rw [e₄, hS₃, h.cnt, show 16 * (t + 1) = 16 * t + 16 by omega]
    exact Avx2.ctr_add _ _ 16
  · have n_st : ¬ (Avx2.stR (est s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
      hp.st_d _ hc (in_dR hk)
    have n_sv : ¬ (saveR s₀).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
      hp.d_b _ (in_dR hk) (save_sub _ _ hc)
    by_cases hin : 1024 * t ≤ k ∧ k < 1024 * t + 1024
    · have ea : edp s₀ + BitVec.ofNat 64 k =
          edp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 (k - 1024 * t) := by
        rw [add_ofNat, Nat.add_sub_cancel' hin.1]
      have x₃ := d₃ (k - 1024 * t) (by omega)
      rw [← ea] at x₃
      rw [f₄ _ (by simpa using n_st), x₃, h.data k hk,
        ite_eq_right (by omega : ¬ k < 1024 * t), ite_eq_left (by omega : k < 1024 * (t + 1)),
        Avx2.plus_block, h.cnt, ks_shift _ hk hin.1]
    · have n_w := out_win hw hk (by omega)
      rw [FA _ (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact n_sv
          · exact n_w
          · exact n_st), h.data k hk]
      by_cases hlt : k < 1024 * t
      · rw [ite_eq_left hlt, ite_eq_left (by omega : k < 1024 * (t + 1))]
      · rw [ite_eq_right hlt, ite_eq_right (by omega : ¬ k < 1024 * (t + 1))]
  · refine incs_frame h.incs FA ?_
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact inc_save _
    · exact dbd.sub_left (inc_sub _)
    · exact (hp.st_b.sub_right (inc_sub _)).symm
  · refine h.frame.trans (FA.sub fun r hr' => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact ⟨Avx2.bufR (ebp s₀), by simp, save_sub _⟩
    · exact ⟨edR s₀, by simp, sw⟩
    · exact ⟨Avx2.stR (est s₀), by simp, fun _ h => h⟩

/-! ## The prologue -/

set_option simprocs false in
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 1024)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.cf = some (decide ((s.gpr .rdx).toNat < 1024)) := by
  have se : BitVec.signExtend 64 (1024 : BitVec 32) = 1024 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  exact ⟨trivial, trivial, trivial, trivial, rfl⟩

/-- The offsets in `buf` and values of the quadwords the prologue stores. -/
def incPairs : List (Nat × BitVec 64) :=
  [(128, 0x0000000100000000), (136, 0x0000000300000002), (144, 0x0000000500000004),
   (152, 0x0000000700000006), (160, 0x0000000900000008), (168, 0x0000000b0000000a),
   (176, 0x0000000d0000000c), (184, 0x0000000f0000000e)]

theorem consts_eq : consts = Avx2.pairsCode incPairs := rfl

theorem incPairs_le : ∀ p ∈ incPairs, p.1 + 8 ≤ 320 := by decide

/-- Read back a stored quadword. -/
local macro "qread" : tactic => `(tactic|
  simp (disch := decide) only [Avx2.storeAll, incPairs, List.foldl_cons, List.foldl_nil,
    Nat.reduceAdd, Avx2.readW64_off, Mem.readW_writeW_self64])

theorem incs_mem (m : Mem) (buf : Addr) : Incs (Avx2.storeAll buf incPairs m) buf := by
  intro j hj
  have E := readW_extract (Avx2.storeAll buf incPairs m) (buf + BitVec.ofNat 64 (128 + 8 * (j / 2)))
    (w := 64) (k := 4 * (j % 2)) (n := 4) (by omega)
  rw [add_ofNat, show 128 + 8 * (j / 2) + 4 * (j % 2) = 4 * (32 + j) by omega] at E
  rw [← E]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨
      j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd]; qread; decide)

theorem prologue_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (consts ++ ([.alu .cmp .rdx (.imm 1024)] : List Instr))) s₀ fun s =>
      LInv s₀ 0 s ∧ s.cf = some (decide (eL s₀ < 1024)) := by
  have hL := eL_lt s₀
  rw [consts_eq]
  refine WP.block_append (WP.mono (Avx2.pairs_ok incPairs incPairs_le (s := s₀) rfl hp.w_b)
    fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => WP.mono (cmp_ok s₁) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  have F : Frame [Avx2.bufR (ebp s₀)] s₀.mem s₂.mem := by
    rw [m₂, m₁]; exact Avx2.storeAll_frame (List.mem_singleton_self _) _ incPairs_le _
  have gk : ∀ r, r ≠ .rax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, g₁ r hr]
  refine ⟨⟨gk _ (by decide), gk _ (by decide), by rw [gk _ (by decide)]; simp,
    by rw [gk _ (by decide)]; simp, by omega, fun r hr => gk r (calleeSaved_ne hr).1,
    by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, fun k hk => ?_, ?_, ?_⟩, ?_⟩
  · rw [Xor.stateAt_frame F (by simpa using hp.st_b), Nat.mul_zero, ctr_zero]
  · rw [F _ (by simpa using fun hc => hp.d_b _ (in_dR hk) hc)]
    simp
  · rw [m₂, m₁]; exact incs_mem _ _
  · exact F.mono (by simp)
  · rw [cf₂, g₁ _ (by decide)]

/-! ## The rest, by `vg_chacha20_xor` -/

section
variable {s₀ : State} {t : Nat}

/-- The data left for `vg_chacha20_xor`. -/
abbrev tR (s₀ : State) (t : Nat) : Region := ⟨edp s₀ + BitVec.ofNat 64 (1024 * t), eL s₀ - 1024 * t⟩

theorem tail_sub (ht : 1024 * t ≤ eL s₀) : Region.Sub (tR s₀ t) (edR s₀) := by
  have hL := eL_lt s₀
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem not_tail {k : Nat} (hk : k < 1024 * t) (ht : 1024 * t ≤ eL s₀) :
    ¬ (tR s₀ t).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := eL_lt s₀
  simp only [Region.Contains]; bv_omega

end

open VG.Proof.ChaCha20.X86_64.Avx2 (stk_ret stk_stk ret_stk vz_ok xor_nosp xor_depth bytes_of_bytesAt)

theorem tail_ok {s₀ : State} (hp : APre s₀) {t : Nat} (hlt : eL s₀ - 1024 * t < 1024) {s : State}
    (h : LInv s₀ t s) :
    WP isa (.seq (.block [.vop .vzeroupper]) (.call "vg_chacha20_xor" Impl.ChaCha20.X86_64.Xor.xor)) s
      fun s' => (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  have hL := eL_lt s₀
  have hle := h.le
  refine WP.seq (WP.mono (vz_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
  have hsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [g₁]; exact h.keep .rsp (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  have hn : (BitVec.ofNat 64 (eL s₀ - 1024 * t)).toNat = eL s₀ - 1024 * t := toNat_ofNat_lt (by omega)
  have hwr : s₁.wr = frR s₀ := by rw [wr₁, h.wr, hp.wr]
  have hrd : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  refine WP.call (k := xorStack 8) Xor.xor_rsi xor_nosp (by rw [xor_depth]; decide)
    (rd := []) (wr := [Avx2.stR (est s₀), tR s₀ t, Avx2.bufR (ebp s₀)]) ?_ ?_ ?_ ?_
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
    · exact ⟨Avx2.stR (est s₀), by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨edR s₀, by simp, 1024 * t, rfl, show 1024 * t + (eL s₀ - 1024 * t) ≤ eL s₀ by omega⟩
    · exact ⟨Avx2.bufR (ebp s₀), by simp, 0, by simp, show 0 + 320 ≤ 320 by omega⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨Avx2.stR (est s₀), by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨edR s₀, by simp, 1024 * t, rfl, show 1024 * t + (eL s₀ - 1024 * t) ≤ eL s₀ by omega⟩
    · exact ⟨Avx2.bufR (ebp s₀), by simp, 0, by simp, show 0 + 320 ≤ 320 by omega⟩
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
      have n_st : ¬ (Avx2.stR (est s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
        hp.st_d _ hc (in_dR hk)
      have n_b : ¬ (Avx2.bufR (ebp s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
        hp.d_b _ (in_dR hk) hc
      have n_sk : ¬ (estk s₀).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
        hp.stk_d _ hc (in_dR hk)
      by_cases hk' : k < 1024 * t
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
            edp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 (k - 1024 * t) := by
          rw [add_ofNat, Nat.add_sub_cancel' (by omega)]
        have x := bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 1024 * t) (by omega)
        rw [← ea, Fce _ (by simpa using n_sk), m₁, h.data k hk2, ite_eq_right hk',
          keystream_getD _ (by omega)] at x
        rw [x, ks_shift _ hk2 (t := t) (by omega)]

/-! ## The whole function -/

theorem xor_eq : Impl.ChaCha20.X86_64.Avx512.xor =
    .seq (.block (consts ++ ([.alu .cmp .rdx (.imm 1024)] : List Instr)))
    (.seq (.ite .b (.block []) (.loop body .ae))
    (.seq (.block [.vop .vzeroupper]) (.call "vg_chacha20_xor" Impl.ChaCha20.X86_64.Xor.xor))) := rfl

theorem correct {s₀ : State} (hp : APre s₀) :
    WP isa Impl.ChaCha20.X86_64.Avx512.xor s₀ fun s' =>
      (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  rw [xor_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, hc⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ t, eL s₀ - 1024 * t < 1024 ∧ LInv s₀ t s) ?_
    fun s₂ ⟨t, ht, h₂⟩ => tail_ok hp ht h₂)
  refine WP.ite (decide (eL s₀ < 1024)) (by simp [eval, hc]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil (M := isa) ⟨0, by omega, h₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s =>
      ∃ t, n = eL s₀ - 1024 * t ∧ 1024 ≤ eL s₀ - 1024 * t ∧ LInv s₀ t s
    have hstep : ∀ n s, Inv n s → WP isa body s (fun s' =>
        (eval .ae s' = some false ∧ ∃ t, eL s₀ - 1024 * t < 1024 ∧ LInv s₀ t s') ∨
        (eval .ae s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨t, rfl, ht, hI⟩
      refine WP.mono (body_ok hp ht hI) fun s' ⟨h', hc'⟩ => ?_
      by_cases hl : eL s₀ - 1024 * (t + 1) < 1024
      · exact .inl ⟨by simp [eval, hc', hl], t + 1, hl, h'⟩
      · exact .inr ⟨by simp [eval, hc', hl], eL s₀ - 1024 * (t + 1), by omega, t + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep (eL s₀ - 1024 * 0) s₁ ⟨0, rfl, by omega, h₁⟩

/-! ## Constant time and the contract -/

/-- `vg_chacha20_xor_avx512` returns with `rsi` pointing at `buf`, as
`vg_chacha20_xor` does, for a caller that recomputes pointers from it. -/
theorem xor_rsi (s : State) (hs : xorAvx2X86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Avx512.xor s t s' ∧ abiPreserved s s' ∧
      (xorAvx2X86_64.post s s' ∧ s'.gpr .rsi = s.gpr .rcx) := by
  obtain ⟨t, s', he, ⟨h, hpost⟩, hr⟩ := correct (Avx2.APre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h, hpost, hr⟩

theorem xor_correct (s : State) (hs : xorAvx2X86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Avx512.xor s t s' ∧ abiPreserved s s' ∧
      xorAvx2X86_64.post s s' :=
  (xor_rsi s hs).imp fun _ ⟨s', he, ha, h, _⟩ => ⟨s', he, ha, h⟩

theorem xor_ct : ConstantTime isa xorAvx2X86_64.pre xorAvx2X86_64.pub
    Impl.ChaCha20.X86_64.Avx512.xor :=
  VG.Taint.constantTime (A := taint) Avx2.τ₀ (fun _ _ h₁ h₂ hp => Avx2.agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem xor_verified :
    Verified X86_64.target Impl.ChaCha20.X86_64.Avx512.xor
      (Spec.ChaCha20.xorContract X86_64.abi 16) :=
  Verified.of_correct xor_correct xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, X86_64.abi, X86_64.argRegs,
      xorAvx2X86_64, Proof.ChaCha20.xorX86_64]
      [Avx2.sat] using Avx2.sat)

end VG.Proof.ChaCha20.X86_64.Avx512
