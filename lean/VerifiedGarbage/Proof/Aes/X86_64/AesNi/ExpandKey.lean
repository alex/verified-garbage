import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.KeySteps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Aes.Contract

/-!
# AES-NI key expansion: the whole function

Untrusted: everything here is checked by Lean. `expandKey_verified` proves
`Impl.Aes.X86_64.AesNi.expandKey` against `expandKeyX86_64`. After each
step, the first `K` words of the schedule are stored (`KS`) and the
registers hold the last words computed; the steps are composed by
induction (`wp_range_flatMap`), each proved once for any index
(`kstepK`, `kstepB6K`).
-/

namespace VG.Proof.Aes.X86_64.AesNi.Key

open VG VG.X86_64
open VG.Proof.Aes.X86_64.AesNi
open VG.Impl.Aes.X86_64.AesNi (at_ kstep kstepB6 rc expand128 expand192 expand256 expandKey)

section
variable (s₀ : State)

abbrev kp : Addr := s₀.gpr .rdi
abbrev len : Nat := (s₀.gpr .rsi).toNat
abbrev sp : Addr := s₀.gpr .rdx
abbrev schR : Region := ⟨sp s₀, 240⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨kp s₀, len s₀⟩]
  wr : s₀.wr = [schR s₀, ⟨s₀.gpr .rcx, 512⟩]
  ret : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (schR s₀)
  len : len s₀ = 16 ∨ len s₀ = 24 ∨ len s₀ = 32

theorem pre_of (s₀ : State) (h : expandKeyX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

/-- Words `0 … K − 1` of the schedule of the `nk`-word key are stored. -/
structure KS (s₀ : State) (nk K : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [schR s₀] s₀.mem s.mem
  good : Good s.mem (sp s₀) (W s₀.mem (kp s₀) nk) K

theorem KS.of_eq {s₀ : State} {nk K K' : Nat} {s : State} (h : KS s₀ nk K s) (e : K = K') :
    KS s₀ nk K' s := e ▸ h

theorem sched_in {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr) (hg : s.gpr = s₀.gpr)
    {off : Nat} (h : off + 16 ≤ 240) :
    InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 (off : Int)) 16 :=
  ⟨schR s₀, by simp [hwr, hp.wr], by rw [hg, ofInt_natCast]; exact contains_offset h (by omega)⟩

theorem key_in {s₀ : State} (hp : Pre s₀) {s : State} (hrd : s.rd = s₀.rd) (hg : s.gpr = s₀.gpr)
    {off : Nat} (h : off + 16 ≤ len s₀) :
    InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 (off : Int)) 16 :=
  ⟨⟨kp s₀, len s₀⟩, by simp [hrd, hp.rd], by
    rw [hg, ofInt_natCast]
    have : len s₀ < 2 ^ 64 := (s₀.gpr .rsi).isLt
    exact contains_offset h (by omega)⟩

/-! ## Words -/

theorem W_plain {m : Mem} {p : Addr} {nk i : Nat} (h0 : 0 < nk) (h : nk ≤ i)
    (hp : ∀ y, temp32 nk i y = y) : W m p nk i = W m p nk (i - nk) ^^^ W m p nk (i - 1) := by
  rw [W_ge h0 h, hp]

theorem temp_plain {nk i : Nat} (h1 : i % nk ≠ 0) (h2 : ¬ (nk > 6 ∧ i % nk = 4)) (y : BitVec 32) :
    temp32 nk i y = y := by
  simp only [temp32, h1, h2, ite_false]

theorem temp_rc {nk i : Nat} (h1 : i % nk = 0) (y : BitVec 32) :
    temp32 nk i y = (sub32 y).rotateRight 8 ^^^ (rc (i / nk)).setWidth 32 := by
  simp only [temp32, h1, ite_true]

theorem temp_sub {nk i : Nat} (h1 : i % nk ≠ 0) (h2 : nk > 6 ∧ i % nk = 4) (y : BitVec 32) :
    temp32 nk i y = sub32 y := by
  have h2' : (nk > 6 ∧ i % nk = 4) = True := eq_true h2
  simp only [temp32, h1, h2', ite_true, ite_false]

theorem dword_bcast (a : BitVec 32) {j : Nat} (hj : j < 4) : dword (ofDwords a a a a) j = a := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> simp

/-- A doubleword of a register loaded from the key. -/
theorem dword_key (m : Mem) (p : Addr) (o j i : Nat) (hj : j < 4) (ho : o + 4 * j = 4 * i) :
    dword (m.readW (p + BitVec.ofInt 64 (o : Int)) 128) j = m.readW (p + BitVec.ofNat 64 (4 * i)) 32 := by
  rw [dword_readW _ _ hj, ofInt_natCast, ← ofNat_add', ho]

theorem psrldq8 (x : BitVec 128) : XShiftOp.eval .psrldq x 8 = x >>> 64 := rfl

theorem dword_shr64 (x : BitVec 128) :
    dword (XShiftOp.eval .psrldq x 8) 0 = dword x 2 ∧ dword (XShiftOp.eval .psrldq x 8) 1 = dword x 3 := by
  rw [psrldq8]
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [getLsbD_dword, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and] <;>
    exact congrArg _ (by omega)

/-- Storing the next `n` words. -/
theorem store_mem {s₀ : State} {nk K n : Nat} {m : Mem} (hf : Frame [schR s₀] s₀.mem m)
    (hg : Good m (sp s₀) (W s₀.mem (kp s₀) nk) K) (v : BitVec 128) (off : Nat) (hoff : off = 4 * K)
    (hn : n ≤ 4) (hv : ∀ j < n, dword v j = W s₀.mem (kp s₀) nk (K + j)) (hK : 4 * K + 16 ≤ 240) :
    Frame [schR s₀] s₀.mem (m.writeW (sp s₀ + BitVec.ofInt 64 (off : Int)) v) ∧
      Good (m.writeW (sp s₀ + BitVec.ofInt 64 (off : Int)) v) (sp s₀) (W s₀.mem (kp s₀) nk) (K + n) := by
  subst hoff
  rw [ofInt_natCast]
  exact ⟨hf.writeW (List.mem_singleton_self _) _ (contains_offset hK (by omega)), good_store hg _ hn hv hK⟩

theorem good_zero (m : Mem) (p : Addr) (f : Nat → BitVec 32) : Good m p f 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

/-! ## The steps -/

/-- `kstep`: from words `a … a + 3` in `d`, words `b … b + 3` (`b = a + Nk`). -/
theorem kstepK {s₀ : State} (hp : Pre s₀) {nk : Nat} (h0 : 0 < nk) (d s : XReg) (sel r : BitVec 8)
    (a b off : Nat) (hb : b = a + nk) (hoff : off = 4 * b) (hK : 4 * b + 16 ≤ 240)
    (hd3 : d ≠ .xmm3) (hd4 : d ≠ .xmm4) {st : State} (hI : KS s₀ nk b st)
    (hA : ∀ j < 4, dword (st.xmm d) j = W s₀.mem (kp s₀) nk (a + j))
    (hT : ∀ j < 4, dword (shufDwords (aesKeygenAssist (st.xmm s) r) sel) j =
      temp32 nk b (W s₀.mem (kp s₀) nk (b - 1)))
    (hres : ∀ j, 0 < j → j < 4 → ∀ y, temp32 nk (b + j) y = y) :
    WP isa (.block (kstep d s sel r off)) st fun st' => KS s₀ nk (b + 4) st' ∧
      (∀ j < 4, dword (st'.xmm d) j = W s₀.mem (kp s₀) nk (b + j)) ∧
      ∀ x, x ≠ d → x ≠ .xmm3 → x ≠ .xmm4 → st'.xmm x = st.xmm x := by
  subst hoff hb
  refine WP.mono (kstep_exec d s sel r _ st hd3 hd4 (sched_in hp hI.wr hI.gpr hK))
    fun st' ⟨hx, hm, hg, hrd, hwr, hxo⟩ => ?_
  have v0 : W s₀.mem (kp s₀) nk (a + nk) =
      W s₀.mem (kp s₀) nk (a + 0) ^^^ temp32 nk (a + nk) (W s₀.mem (kp s₀) nk (a + nk - 1)) := by
    rw [W_ge h0 (by omega), Nat.add_sub_cancel, Nat.add_zero]
  have vj : ∀ j, 0 < j → j < 4 → W s₀.mem (kp s₀) nk (a + nk + j) =
      W s₀.mem (kp s₀) nk (a + j) ^^^ W s₀.mem (kp s₀) nk (a + nk + (j - 1)) := fun j h1 h2 => by
    rw [W_plain h0 (by omega) (hres j h1 h2), show a + nk + j - nk = a + j by omega,
      show a + nk + j - 1 = a + nk + (j - 1) by omega]
  have v1 := vj 1 (by omega) (by omega)
  have v2 := vj 2 (by omega) (by omega)
  have v3 := vj 3 (by omega) (by omega)
  simp only [Nat.reduceSub, Nat.add_zero] at v1 v2 v3
  obtain ⟨e0, e1, e2, e3⟩ := dword_kv (st.xmm d) (shufDwords (aesKeygenAssist (st.xmm s) r) sel)
  have hv : ∀ j < 4, dword (kv (st.xmm d) (shufDwords (aesKeygenAssist (st.xmm s) r) sel)) j =
      W s₀.mem (kp s₀) nk (a + nk + j) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · show _ = W s₀.mem (kp s₀) nk (a + nk)
      rw [e0, hA 0 (by omega), hT 0 (by omega), v0]
    · rw [e1, hA 1 (by omega), hA 0 (by omega), hT 1 (by omega), v1, v0]
    · rw [e2, hA 2 (by omega), hA 1 (by omega), hA 0 (by omega), hT 2 (by omega), v2, v1, v0]
    · rw [e3, hA 3 (by omega), hA 2 (by omega), hA 1 (by omega), hA 0 (by omega), hT 3 (by omega),
        v3, v2, v1, v0]
  refine ⟨⟨hg.trans hI.gpr, hrd.trans hI.rd, hwr.trans hI.wr, ?_, ?_⟩, fun j hj => by rw [hx]; exact hv j hj,
    hxo⟩
  · rw [hm, hI.gpr, ofInt_natCast]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (contains_offset hK (by omega))
  · rw [hm, hI.gpr, ofInt_natCast]
    exact good_store hI.good _ (Nat.le_refl 4) hv hK

/-- `kstepB6`: from words `b − 6`, `b − 5` in `xmm2` and `b − 1` in `xmm1`'s
last doubleword, words `b`, `b + 1` in `xmm2`. -/
theorem kstepB6K {s₀ : State} (hp : Pre s₀) (c b off : Nat) (hc : c % 6 = 4) (hb : b = c + 6) (hoff : off = 4 * b)
    (hK : 4 * b + 16 ≤ 240) {st : State} (hI : KS s₀ 6 b st)
    (hB0 : dword (st.xmm .xmm2) 0 = W s₀.mem (kp s₀) 6 c)
    (hB1 : dword (st.xmm .xmm2) 1 = W s₀.mem (kp s₀) 6 (c + 1))
    (hA3 : dword (st.xmm .xmm1) 3 = W s₀.mem (kp s₀) 6 (c + 5)) :
    WP isa (.block (kstepB6 off)) st fun st' => KS s₀ 6 (b + 2) st' ∧
      dword (st'.xmm .xmm2) 0 = W s₀.mem (kp s₀) 6 b ∧
      dword (st'.xmm .xmm2) 1 = W s₀.mem (kp s₀) 6 (b + 1) ∧
      ∀ x, x ≠ .xmm2 → x ≠ .xmm3 → x ≠ .xmm4 → st'.xmm x = st.xmm x := by
  subst hoff hb
  refine WP.mono (kstepB6_exec _ st (sched_in hp hI.wr hI.gpr hK))
    fun st' ⟨hx, hm, hg, hrd, hwr, hxo⟩ => ?_
  have v0 : W s₀.mem (kp s₀) 6 (c + 6) = W s₀.mem (kp s₀) 6 c ^^^ W s₀.mem (kp s₀) 6 (c + 5) := by
    rw [W_plain (by decide) (by omega) (temp_plain (by omega) (by omega)),
      show c + 6 - 6 = c by omega, show c + 6 - 1 = c + 5 by omega]
  have v1 : W s₀.mem (kp s₀) 6 (c + 6 + 1) =
      W s₀.mem (kp s₀) 6 (c + 1) ^^^ W s₀.mem (kp s₀) 6 (c + 6) := by
    rw [W_plain (by decide) (by omega) (temp_plain (by omega) (by omega)),
      show c + 6 + 1 - 6 = c + 1 by omega, show c + 6 + 1 - 1 = c + 6 by omega]
  obtain ⟨e0, e1⟩ := dword_kb (st.xmm .xmm2) (shufDwords (st.xmm .xmm1) 0xff)
  have t : ∀ j < 4, dword (shufDwords (st.xmm .xmm1) 0xff) j = W s₀.mem (kp s₀) 6 (c + 5) :=
    fun j hj => by rw [shuf_ff, dword_bcast _ hj, hA3]
  have hv : ∀ j < 2, dword (kb (st.xmm .xmm2) (shufDwords (st.xmm .xmm1) 0xff)) j =
      W s₀.mem (kp s₀) 6 (c + 6 + j) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rw [e0, hB0, t 0 (by omega), Nat.add_zero, v0]
    · rw [e1, hB1, hB0, t 1 (by omega), v1, v0]
  refine ⟨⟨hg.trans hI.gpr, hrd.trans hI.rd, hwr.trans hI.wr, ?_, ?_⟩,
    by rw [hx]; exact hv 0 (by omega), by rw [hx]; exact hv 1 (by omega), hxo⟩
  · rw [hm, hI.gpr, ofInt_natCast]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (contains_offset hK (by omega))
  · rw [hm, hI.gpr, ofInt_natCast]
    exact good_store hI.good _ (by decide) hv hK

/-! ## AES-128 -/

/-- After `k` steps: words `0 … 4k + 3` stored, `4k … 4k + 3` in `xmm1`. -/
def Inv128 (s₀ : State) (k : Nat) (st : State) : Prop :=
  KS s₀ 4 (4 * k + 4) st ∧ ∀ j < 4, dword (st.xmm .xmm1) j = W s₀.mem (kp s₀) 4 (4 * k + j)

theorem expand128_ok {s₀ : State} (hp : Pre s₀) (hl : len s₀ = 16) {st : State}
    (hf : XFrame [] s₀ st) : WP isa (.block expand128) st (KS s₀ 4 44) := by
  rw [expand128, WP.block_append_iff]
  have hin := key_in hp (s := s₀) rfl rfl (off := 0) (by omega)
  have hw := sched_in hp (s := s₀) rfl rfl (off := 0) (by omega)
  refine WP.mono (Q := Inv128 s₀ 0) ?_ fun st₁ h₁ => WP.mono
    (wp_range_flatMap (Inv128 s₀) (fun k st hk h => ?_) 10 (Nat.le_refl _) st₁ h₁) fun _ h => h.1
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, isa,
      State.setXmm, State.load128, State.store128, ea_at, hf.gpr, hf.rd, hf.wr, hf.mem, hin, hw,
      ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
    have hv : ∀ j < 4, dword (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 128) j =
        W s₀.mem (kp s₀) 4 (0 + j) := fun j hj => by
      rw [dword_key _ _ 0 j (0 + j) hj (by omega), W_lt (by omega)]
    obtain ⟨f₁, g₁⟩ := store_mem (Frame.refl _ _) (good_zero _ _ _) _ 0 rfl (Nat.le_refl 4) hv (by decide)
    exact ⟨⟨rfl, rfl, rfl, f₁, g₁.mono (by omega)⟩, fun j hj => (hv j hj).trans (congrArg _ (by omega))⟩
  · refine WP.mono (kstepK hp (nk := 4) (by decide) .xmm1 .xmm1 0xff (rc (k + 1)) (4 * k) (4 * (k + 1)) _
      (by omega) (by omega) (by omega) (by decide) (by decide) (h.1.of_eq (by omega)) h.2
      (fun j hj => ?_) (fun j h1 h2 y => temp_plain (by omega) (by omega) y))
      fun st' ⟨hI', hA', _⟩ => ⟨hI'.of_eq (by omega), hA'⟩
    rw [shuf_ff, dword_bcast _ hj, kga3, h.2 3 (by omega), temp_rc (by omega),
      show 4 * (k + 1) / 4 = k + 1 by omega, show 4 * (k + 1) - 1 = 4 * k + 3 by omega]

/-! ## AES-192 -/

/-- After `k` steps: words `0 … 6k + 5` stored, `6k … 6k + 3` in `xmm1`,
`6k + 4` and `6k + 5` in `xmm2`. -/
def Inv192 (s₀ : State) (k : Nat) (st : State) : Prop :=
  KS s₀ 6 (6 * k + 6) st ∧ (∀ j < 4, dword (st.xmm .xmm1) j = W s₀.mem (kp s₀) 6 (6 * k + j)) ∧
    dword (st.xmm .xmm2) 0 = W s₀.mem (kp s₀) 6 (6 * k + 4) ∧
    dword (st.xmm .xmm2) 1 = W s₀.mem (kp s₀) 6 (6 * k + 5)

theorem hT55 {s₀ : State} {st : State} {b k : Nat} (hb : b = 6 * k + 6)
    (h : dword (st.xmm .xmm2) 1 = W s₀.mem (kp s₀) 6 (b - 1)) :
    ∀ j < 4, dword (shufDwords (aesKeygenAssist (st.xmm .xmm2) (rc (k + 1))) 0x55) j =
      temp32 6 b (W s₀.mem (kp s₀) 6 (b - 1)) := fun j hj => by
  rw [shuf_55, dword_bcast _ hj, kga1, h, temp_rc (by omega), show b / 6 = k + 1 by omega]

theorem expand192_ok {s₀ : State} (hp : Pre s₀) (hl : len s₀ = 24) {st : State}
    (hf : XFrame [] s₀ st) : WP isa (.block expand192) st (KS s₀ 6 52) := by
  simp only [expand192, List.append_assoc]
  rw [WP.block_append_iff]
  have hin0 := key_in hp (s := s₀) rfl rfl (off := 0) (by omega)
  have hin8 := key_in hp (s := s₀) rfl rfl (off := 8) (by omega)
  have hw0 := sched_in hp (s := s₀) rfl rfl (off := 0) (by omega)
  have hw16 := sched_in hp (s := s₀) rfl rfl (off := 16) (by omega)
  refine WP.mono (Q := Inv192 s₀ 0) ?_ fun st₁ h₁ => WP.block_append_iff.mpr (WP.mono
    (wp_range_flatMap (Inv192 s₀) (fun k st hk h => ?_) 7 (Nat.le_refl _) st₁ h₁) fun st₂ h => ?_)
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, isa,
      XOp.exec, State.setXmm, State.load128, State.store128, ea_at, hf.gpr, hf.rd, hf.wr, hf.mem,
      hin0, hin8, hw0, hw16, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
    have hv : ∀ j < 4, dword (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 128) j =
        W s₀.mem (kp s₀) 6 (0 + j) := fun j hj => by
      rw [dword_key _ _ 0 j (0 + j) hj (by omega), W_lt (by omega)]
    have hB : ∀ j < 2, dword (XShiftOp.eval .psrldq
        (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 128) 8) j =
        W s₀.mem (kp s₀) 6 (4 + j) := fun j hj => by
      obtain ⟨e0, e1⟩ := dword_shr64 (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 128)
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rw [e0, dword_key _ _ 8 2 4 (by omega) (by omega), W_lt (by omega)]
      · rw [e1, dword_key _ _ 8 3 5 (by omega) (by omega), W_lt (by omega)]
    obtain ⟨f₁, g₁⟩ := store_mem (Frame.refl _ _) (good_zero _ _ _) _ 0 rfl (Nat.le_refl 4) hv (by decide)
    obtain ⟨f₂, g₂⟩ := store_mem f₁ g₁ _ 16 rfl (by decide) hB (by decide)
    exact ⟨⟨rfl, rfl, rfl, f₂, g₂.mono (by omega)⟩, fun j hj => (hv j hj).trans (congrArg _ (by omega)),
      hB 0 (by omega), hB 1 (by omega)⟩
  · rw [WP.block_append_iff]
    refine WP.mono (kstepK hp (nk := 6) (by decide) .xmm1 .xmm2 0x55 (rc (k + 1)) (6 * k) (6 * k + 6) _
      (by omega) (by omega) (by omega) (by decide) (by decide) h.1 h.2.1
      (hT55 rfl (h.2.2.2.trans (congrArg _ (by omega))))
      (fun j h1 h2 y => temp_plain (by omega) (by omega) y)) fun st₁ ⟨hI₁, hA₁, hx₁⟩ => ?_
    have hx2 := hx₁ .xmm2 (by decide) (by decide) (by decide)
    refine WP.mono (kstepB6K hp (6 * k + 4) (6 * k + 6 + 4) _ (by omega) (by omega) (by omega) (by omega)
      hI₁ (by rw [hx2]; exact h.2.2.1) (by rw [hx2]; exact h.2.2.2.trans (congrArg _ (by omega)))
      ((hA₁ 3 (by omega)).trans (congrArg _ (by omega)))) fun st₂ ⟨hI₂, hb0, hb1, hx₂⟩ =>
      ⟨hI₂.of_eq (by omega), fun j hj => ?_, hb0.trans (congrArg _ (by omega)),
        hb1.trans (congrArg _ (by omega))⟩
    rw [hx₂ .xmm1 (by decide) (by decide) (by decide)]
    exact (hA₁ j hj).trans (congrArg _ (by omega))
  · refine WP.mono (kstepK hp (nk := 6) (by decide) .xmm1 .xmm2 0x55 (rc 8) (6 * 7) (6 * 7 + 6) 192
      (by omega) (by omega) (by omega) (by decide) (by decide) h.1 h.2.1
      (hT55 (k := 7) rfl (h.2.2.2.trans (congrArg _ (by omega))))
      (fun j h1 h2 y => temp_plain (by omega) (by omega) y)) fun st' ⟨hI', _, _⟩ => hI'.of_eq (by omega)

/-! ## AES-256 -/

/-- After `k` steps: words `0 … 8k + 7` stored, `8k … 8k + 3` in `xmm1`,
`8k + 4 … 8k + 7` in `xmm2`. -/
def Inv256 (s₀ : State) (k : Nat) (st : State) : Prop :=
  KS s₀ 8 (8 * k + 8) st ∧ (∀ j < 4, dword (st.xmm .xmm1) j = W s₀.mem (kp s₀) 8 (8 * k + j)) ∧
    ∀ j < 4, dword (st.xmm .xmm2) j = W s₀.mem (kp s₀) 8 (8 * k + 4 + j)

theorem hTff {s₀ : State} {st : State} {b k : Nat} (hb : b = 8 * k + 8)
    (h : dword (st.xmm .xmm2) 3 = W s₀.mem (kp s₀) 8 (b - 1)) :
    ∀ j < 4, dword (shufDwords (aesKeygenAssist (st.xmm .xmm2) (rc (k + 1))) 0xff) j =
      temp32 8 b (W s₀.mem (kp s₀) 8 (b - 1)) := fun j hj => by
  rw [shuf_ff, dword_bcast _ hj, kga3, h, temp_rc (by omega), show b / 8 = k + 1 by omega]

theorem expand256_ok {s₀ : State} (hp : Pre s₀) (hl : len s₀ = 32) {st : State}
    (hf : XFrame [] s₀ st) : WP isa (.block expand256) st (KS s₀ 8 60) := by
  simp only [expand256, List.append_assoc]
  rw [WP.block_append_iff]
  have hin0 := key_in hp (s := s₀) rfl rfl (off := 0) (by omega)
  have hin16 := key_in hp (s := s₀) rfl rfl (off := 16) (by omega)
  have hw0 := sched_in hp (s := s₀) rfl rfl (off := 0) (by omega)
  have hw16 := sched_in hp (s := s₀) rfl rfl (off := 16) (by omega)
  refine WP.mono (Q := Inv256 s₀ 0) ?_ fun st₁ h₁ => WP.block_append_iff.mpr (WP.mono
    (wp_range_flatMap (Inv256 s₀) (fun k st hk h => ?_) 6 (Nat.le_refl _) st₁ h₁) fun st₂ h => ?_)
  · apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, isa,
      State.setXmm, State.load128, State.store128, ea_at, hf.gpr, hf.rd, hf.wr, hf.mem, hin0, hin16,
      hw0, hw16, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
    have hv : ∀ j < 4, dword (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 128) j =
        W s₀.mem (kp s₀) 8 (0 + j) := fun j hj => by
      rw [dword_key _ _ 0 j (0 + j) hj (by omega), W_lt (by omega)]
    have hB : ∀ j < 4, dword (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((16 : Nat) : Int)) 128) j =
        W s₀.mem (kp s₀) 8 (4 + j) := fun j hj => by
      rw [dword_key _ _ 16 j (4 + j) hj (by omega), W_lt (by omega)]
    obtain ⟨f₁, g₁⟩ := store_mem (Frame.refl _ _) (good_zero _ _ _) _ 0 rfl (Nat.le_refl 4) hv (by decide)
    obtain ⟨f₂, g₂⟩ := store_mem f₁ g₁ _ 16 rfl (Nat.le_refl 4) hB (by decide)
    exact ⟨⟨rfl, rfl, rfl, f₂, g₂.mono (by omega)⟩, fun j hj => (hv j hj).trans (congrArg _ (by omega)),
      fun j hj => (hB j hj).trans (congrArg _ (by omega))⟩
  · rw [WP.block_append_iff]
    refine WP.mono (kstepK hp (nk := 8) (by decide) .xmm1 .xmm2 0xff (rc (k + 1)) (8 * k) (8 * k + 8) _
      (by omega) (by omega) (by omega) (by decide) (by decide) h.1 h.2.1
      (hTff rfl ((h.2.2 3 (by omega)).trans (congrArg _ (by omega))))
      (fun j h1 h2 y => temp_plain (by omega) (by omega) y)) fun st₁ ⟨hI₁, hA₁, hx₁⟩ => ?_
    have hx2 := hx₁ .xmm2 (by decide) (by decide) (by decide)
    refine WP.mono (kstepK hp (nk := 8) (by decide) .xmm2 .xmm1 0xaa 0 (8 * k + 4) (8 * k + 8 + 4) _
      (by omega) (by omega) (by omega) (by decide) (by decide) hI₁ (fun j hj => by rw [hx2]; exact h.2.2 j hj)
      (fun j hj => by
        rw [shuf_aa, dword_bcast _ hj, kga2, hA₁ 3 (by omega), temp_sub (by omega) (by omega),
          show 8 * k + 8 + 4 - 1 = 8 * k + 8 + 3 by omega])
      (fun j h1 h2 y => temp_plain (by omega) (by omega) y)) fun st₂ ⟨hI₂, hA₂, hx₂⟩ =>
      ⟨hI₂.of_eq (by omega), fun j hj => ?_, fun j hj => (hA₂ j hj).trans (congrArg _ (by omega))⟩
    rw [hx₂ .xmm1 (by decide) (by decide) (by decide)]
    exact (hA₁ j hj).trans (congrArg _ (by omega))
  · refine WP.mono (kstepK hp (nk := 8) (by decide) .xmm1 .xmm2 0xff (rc 7) (8 * 6) (8 * 6 + 8) 224
      (by omega) (by omega) (by omega) (by decide) (by decide) h.1 h.2.1
      (hTff (k := 6) rfl ((h.2.2 3 (by omega)).trans (congrArg _ (by omega))))
      (fun j h1 h2 y => temp_plain (by omega) (by omega) y)) fun st' ⟨hI', _, _⟩ => hI'.of_eq (by omega)

/-! ## The whole function -/

theorem fin {s₀ : State} (hp : Pre s₀) {nk : Nat} (h0 : 0 < nk) (hl : len s₀ = 4 * nk) {st : State}
    (hI : KS s₀ nk (4 * (nk + 7)) st) : gprPreserved s₀ st ∧ expandKeyX86_64.post s₀ st := by
  refine ⟨⟨fun r _ => by rw [hI.gpr], hI.frame.readW (Region.contains_self _ _)
    (by simpa using hp.ret) (by decide)⟩, ?_⟩
  have hl' : (s₀.gpr .rsi).toNat = 4 * nk := hl
  show Spec.Aes.bytesAt st.mem (sp s₀) (16 * (Spec.Aes.rounds ((s₀.gpr .rsi).toNat / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem (kp s₀) (s₀.gpr .rsi).toNat)
  rw [hl', show 4 * nk / 4 = nk by omega, expandKey_eq s₀.mem _ h0, Spec.Aes.rounds,
    show 16 * (nk + 6 + 1) = 4 * (4 * (nk + 6 + 1)) by omega]
  exact bytesAt_eq st.mem _ _ _ fun i hi => hI.good i (by omega)

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa expandKey s₀ fun s' => gprPreserved s₀ s' ∧ expandKeyX86_64.post s₀ s' := by
  have hrsi : s₀.gpr .rsi = BitVec.ofNat 64 (len s₀) := by simp [len]
  refine WP.seq (WP.mono (cmpRsi_ok s₀ 24 _ hrsi) fun s₁ ⟨hz₁, hf₁⟩ => ?_)
  refine WP.ite (decide (len s₀ = 24)) (by
    rw [show isa.eval .e s₁ = s₁.zf from rfl, hz₁]
    rcases hp.len with h | h | h <;> rw [h] <;> decide) (fun h => ?_) (fun h => ?_)
  · have h24 : len s₀ = 24 := by simpa using h
    exact WP.mono (expand192_ok hp h24 hf₁) fun _ hI => fin hp (nk := 6) (by decide) h24 hI
  · refine WP.seq (WP.mono (cmpRsi_ok s₁ 32 (len s₀) (by rw [hf₁.gpr]; exact hrsi)) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
    have hf := (hf₁.comp hf₂).mono (rs' := []) (by simp)
    refine WP.ite (decide (len s₀ = 32)) (by
      rw [show isa.eval .e s₂ = s₂.zf from rfl, hz₂]
      rcases hp.len with h | h | h <;> rw [h] <;> decide) (fun h' => ?_) (fun h' => ?_)
    · have h32 : len s₀ = 32 := by simpa using h'
      exact WP.mono (expand256_ok hp h32 hf) fun _ hI => fin hp (nk := 8) (by decide) h32 hI
    · have h16 : len s₀ = 16 := by
        simp only [decide_eq_false_iff_not] at h h'; rcases hp.len with e | e | e <;> omega
      exact WP.mono (expand128_ok hp h16 hf) fun _ hI => fin hp (nk := 4) (by decide) h16 hI

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩, ⟨0x3000, 512⟩]

theorem expandKey_correct (s : State) (hs : expandKeyX86_64.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem expandKey_ct : ConstantTime isa expandKeyX86_64.pre expandKeyX86_64.pub expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem expandKey_verified :
    Verified X86_64.target Impl.Aes.X86_64.AesNi.expandKey (Spec.Aes.expandKeyContract X86_64.abi) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig,
      Proof.Aes.X86_64.AesNi.expandKeyX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Aes.X86_64.AesNi.Key.satState] using Proof.Aes.X86_64.AesNi.Key.satState)

end VG.Proof.Aes.X86_64.AesNi.Key
