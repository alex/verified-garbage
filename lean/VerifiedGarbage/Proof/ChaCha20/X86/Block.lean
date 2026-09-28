import VerifiedGarbage.Proof.ChaCha20.X86.Rounds
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Spec.ChaCha20.X86

/-!
# ChaCha20 block function on x86 (32-bit): the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20.X86

open VG VG.X86 VG.Impl.ChaCha20.X86 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word stateAt innerBlock)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev esp₀ : BitVec 32 := s₀.gpr .esp
/-- The two pointers. -/
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
/-- Their 64-bit addresses. -/
abbrev SA : Addr := (st s₀).setWidth 64
abbrev BA : Addr := (bp s₀).setWidth 64
abbrev stR : Region := ⟨SA s₀, 64⟩
abbrev bufR : Region := ⟨BA s₀, 256⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- The input state. -/
abbrev V : CState := stateAt s₀.mem (SA s₀)
/-- The result of the rounds. -/
abbrev Rs : CState := Nat.repeat innerBlock 10 (V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [stR s₀, argR s₀]
  wr : s₀.wr = [bufR s₀]
  buf_st : (bufR s₀).Disjoint (stR s₀)
  arg_buf : (argR s₀).Disjoint (bufR s₀)
  ret_buf : (retR s₀).Disjoint (bufR s₀)
  st_fits : (st s₀).toNat + 64 ≤ 2 ^ 32
  buf_fits : (bp s₀).toNat + 256 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 12 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Spec.ChaCha20.blockX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, toNat_ofNat_lt ho]
  exact h

/-- A sub-range `[a, a + len)` of `buf` contains `[d, d + n)`. -/
theorem contains_sub (p : Addr) {a len d n : Nat} (h1 : a ≤ d) (h2 : d + n ≤ a + len)
    (h3 : a + len < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains]
  rw [show p + BitVec.ofNat 64 d - (p + BitVec.ofNat 64 a) = BitVec.ofNat 64 (d - a) by bv_omega,
    toNat_ofNat_lt (by omega)]
  omega

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem eaB {d : Nat} (hd : d < 256) : addr (bp s₀) d = BA s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.buf_fits; omega)

theorem eaS {d : Nat} (hd : d < 64) : addr (st s₀) d = SA s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fits; omega)

theorem eaA {d : Nat} (hd : d < 12) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.esp_fits; omega)

theorem hw : bufR s₀ ∈ s₀.wr := by simp [hp.wr]

theorem in_buf {d n : Nat} (h : d + n ≤ 256) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

theorem out_buf {d n : Nat} (h : d + n ≤ 256) : InRegions s₀.wr (BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bufR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

theorem in_st {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (SA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [hp.rd], contains_off (by omega) (by omega)⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 2) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  intro a ha
  simp only [Region.Contains, argAddr] at ha ⊢
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    hp.eaA (by omega)]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (esp₀ s₀) (4 + 4 * i)
    from rfl, hp.eaA (by omega)] at ha
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem arg_contains {i : Nat} (hi : i < 2) : (argR s₀).Contains (argAddr s₀ i) 4 := by
  simp only [argR]
  rw [show argAddr s₀ i = addr (esp₀ s₀) (4 + 4 * i) from rfl, hp.eaA (by omega),
    show argAddr s₀ 0 = addr (esp₀ s₀) 4 from rfl, hp.eaA (by omega)]
  exact contains_sub _ (by omega) (by omega) (by omega)

theorem in_arg {i : Nat} (hi : i < 2) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨argR s₀, by simp [hp.rd], hp.arg_contains hi⟩

/-- Reading the input state after writes to `buf` only. -/
theorem read_st {m : Mem} (hf : Frame [bufR s₀] s₀.mem m) {k : Nat} (hk : k < 16) :
    m.readW (SA s₀ + BitVec.ofNat 64 (4 * k)) 32 = (V s₀)[k] := by
  rw [hf.readW (r := stR s₀) (contains_off (by omega) (by omega)) (by simpa using hp.buf_st.symm)
    (by decide)]
  simp only [V, stateAt, Vector.getElem_ofFn]

end Pre

theorem workR_sub (B : Addr) : Region.Sub (workR B) ⟨B, 256⟩ := Region.sub_prefix (by omega)

theorem frame_buf {s₀ : State} {m m' : Mem} (hf : Frame [workR (BA s₀)] m m') :
    Frame [bufR s₀] m m' :=
  hf.sub fun r hr => ⟨bufR s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact workR_sub _⟩

/-! ## Saving the callee-saved registers, and loading the pointers -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  ((s₀.mem.writeW (BA s₀ + BitVec.ofNat 64 64) (s₀.gpr .ebx)).writeW (BA s₀ + BitVec.ofNat 64 68)
    (s₀.gpr .esi)).writeW (BA s₀ + BitVec.ofNat 64 72) (s₀.gpr .edi)

/-- The callee-saved registers `ebx, esi, edi` are saved in `buf`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (BA s₀ + BitVec.ofNat 64 64) 32 = s₀.gpr .ebx ∧
  m.readW (BA s₀ + BitVec.ofNat 64 68) 32 = s₀.gpr .esi ∧
  m.readW (BA s₀ + BitVec.ofNat 64 72) 32 = s₀.gpr .edi

theorem off_sep (p : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    Mem.Sep (p + BitVec.ofNat 64 d) 4 (p + BitVec.ofNat 64 e) 4 := by
  intro x hx hy
  bv_omega

theorem readW_writeW_off (m : Mem) (p : Addr) (v : Word) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 =
      m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (off_sep p hd he h) (by decide)

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_⟩
  · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega),
      readW_writeW_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem saveMem_frame (s₀ : State) : Frame [bufR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 256 → (bufR s₀).Contains (BA s₀ + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => contains_off hd (by omega)
  simp only [saveMem]
  exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 64 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 68 (by omega))).writeW (List.mem_singleton_self _) _
    (c 72 (by omega))

/-- The saved registers survive writes to the working state. -/
theorem saved_frame {s₀ : State} {m m' : Mem} (h : Saved s₀ m) (hf : Frame [workR (BA s₀)] m m') :
    Saved s₀ m' := by
  have key : ∀ d : Nat, 64 ≤ d → d + 4 ≤ 76 →
      m'.readW (BA s₀ + BitVec.ofNat 64 d) 32 = m.readW (BA s₀ + BitVec.ofNat 64 d) 32 := by
    intro d h1 h2
    refine hf.readW (r := ⟨BA s₀ + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    bv_omega
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨(key 64 (by omega) (by omega)).trans h1, (key 68 (by omega) (by omega)).trans h2,
    (key 72 (by omega) (by omega)).trans h3⟩

set_option maxHeartbeats 0 in
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block save) s₀ fun s₁ =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₁.gpr r = s₀.gpr r) ∧
      s₁.gpr .esi = bp s₀ ∧ s₁.gpr .edi = st s₀ ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.mem = saveMem s₀ := by
  have i8 : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 4 :=
    hp.in_arg (i := 1) (by omega)
  have i4 : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 4 :=
    hp.in_arg (i := 0) (by omega)
  have v8 : s₀.mem.readW ((s₀.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 32 = bp s₀ := rfl
  have v4 : s₀.mem.readW ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 32 = st s₀ := rfl
  have e64 : (bp s₀ + BitVec.ofNat 32 64).setWidth 64 = BA s₀ + BitVec.ofNat 64 64 := hp.eaB (by omega)
  have e68 : (bp s₀ + BitVec.ofNat 32 68).setWidth 64 = BA s₀ + BitVec.ofNat 64 68 := hp.eaB (by omega)
  have e72 : (bp s₀ + BitVec.ofNat 32 72).setWidth 64 = BA s₀ + BitVec.ofNat 64 72 := hp.eaB (by omega)
  have o64 := hp.out_buf (d := 64) (n := 4) (by omega)
  have o68 := hp.out_buf (d := 68) (n := 4) (by omega)
  have o72 := hp.out_buf (d := 72) (n := 4) (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [save, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg,
    State.ea, at_, State.load32, State.store32, i8, i4, v8, v4, e64, e68, e72, o64, o68, o72,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4], by simp, by simp, trivial, trivial, rfl⟩

/-! ## Copying the state -/

/-- The copy invariant after `n` words, relative to the state `s₁` after the prologue. -/
structure CI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  keep : ∀ r, r ≠ .eax → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  fb : Frame [bufR s₀] s₀.mem s.mem
  fw : Frame [workR (BA s₀)] s₁.mem s.mem
  copied : ∀ j (hj : j < 16), j < n → s.mem.readW (wordAddr (BA s₀) j) 32 = (V s₀)[j]

set_option maxHeartbeats 400000 in
theorem copy_step {s₀ s₁ : State} (hp : Pre s₀) (hesi : s₁.gpr .esi = bp s₀)
    (hedi : s₁.gpr .edi = st s₀) {n : Nat} (hn : n < 16) {s : State} (hc : CI s₀ s₁ n s) :
    WP isa (.block (copyWord n)) s (CI s₀ s₁ (n + 1)) := by
  have hsi : s.gpr .esi = bp s₀ := (hc.keep _ (by decide)).trans hesi
  have hdi : s.gpr .edi = st s₀ := (hc.keep _ (by decide)).trans hedi
  have eS : (st s₀ + BitVec.ofNat 32 (4 * n)).setWidth 64 = SA s₀ + BitVec.ofNat 64 (4 * n) :=
    hp.eaS (by omega)
  have eB : (bp s₀ + BitVec.ofNat 32 (4 * n)).setWidth 64 = wordAddr (BA s₀) n := hp.eaB (by omega)
  have iS : InRegions (s.rd ++ s.wr) (SA s₀ + BitVec.ofNat 64 (4 * n)) 4 := by
    rw [hc.rd, hc.wr]; exact hp.in_st hn _
  have oB : InRegions s.wr (wordAddr (BA s₀) n) 4 := by rw [hc.wr]; exact hp.out_buf (by omega)
  have hv := hp.read_st hc.fb hn
  apply WP.of_runBlock
  simp (config := {decide := true}) only [copyWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg,
    State.ea, at_, State.load32, State.store32, hsi, hdi, eS, eB, iS, oB, hv, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => by simp [hr, hc.keep r hr], hc.rd, hc.wr,
    hc.fb.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega)),
    hc.fw.writeW (List.mem_singleton_self _) _ (word_in_work _ hn), fun j hj hjn => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
  · rw [readW_writeW_word _ _ _ hj hn (by omega)]; exact hc.copied j hj hjn
  · exact Mem.readW_writeW_self32 _ _ _

/-! ## Adding the input state -/

/-- The add invariant after `n` words, relative to the state `sB` after the rounds. -/
structure AI (s₀ sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (wordAddr (BA s₀) j) 32 =
    if j < n then (Rs s₀)[j] + (V s₀)[j] else (Rs s₀)[j]
  keep : ∀ r, r ≠ .eax → s.gpr r = sB.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  fb : Frame [bufR s₀] s₀.mem s.mem
  fw : Frame [workR (BA s₀)] sB.mem s.mem

set_option maxHeartbeats 400000 in
theorem add_step {s₀ sB : State} (hp : Pre s₀) (hesi : sB.gpr .esi = bp s₀)
    (hedi : sB.gpr .edi = st s₀) {n : Nat} (hn : n < 16) {s : State} (ha : AI s₀ sB n s) :
    WP isa (.block (addWord n)) s (AI s₀ sB (n + 1)) := by
  have hsi : s.gpr .esi = bp s₀ := (ha.keep _ (by decide)).trans hesi
  have hdi : s.gpr .edi = st s₀ := (ha.keep _ (by decide)).trans hedi
  have eS : (st s₀ + BitVec.ofNat 32 (4 * n)).setWidth 64 = SA s₀ + BitVec.ofNat 64 (4 * n) :=
    hp.eaS (by omega)
  have eB : (bp s₀ + BitVec.ofNat 32 (4 * n)).setWidth 64 = wordAddr (BA s₀) n := hp.eaB (by omega)
  have iS : InRegions (s.rd ++ s.wr) (SA s₀ + BitVec.ofNat 64 (4 * n)) 4 := by
    rw [ha.rd, ha.wr]; exact hp.in_st hn _
  have iB : InRegions (s.rd ++ s.wr) (wordAddr (BA s₀) n) 4 := by
    rw [ha.wr]; exact hp.in_buf (by omega) _
  have oB : InRegions s.wr (wordAddr (BA s₀) n) 4 := by rw [ha.wr]; exact hp.out_buf (by omega)
  have hv := hp.read_st ha.fb hn
  have hr := ha.out n hn
  simp only [lt_irrefl, ite_false] at hr
  apply WP.of_runBlock
  simp (config := {decide := true}) only [addWord, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.setReg, arithFlags, State.setFlags, State.ea, at_, State.load32, State.store32, hsi, hdi,
    eS, eB, iS, iB, oB, hv, hr, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj => ?_, fun r hr => by simp [hr, ha.keep r hr], ha.rd, ha.wr,
    ha.fb.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega)),
    ha.fw.writeW (List.mem_singleton_self _) _ (word_in_work _ hn)⟩
  by_cases hjn : j = n
  · subst hjn; simp [Mem.readW_writeW_self32]
  · rw [readW_writeW_word _ _ _ hj hn hjn, ha.out j hj]
    split <;> split <;> first | omega | rfl

/-! ## Restoring the callee-saved registers -/

set_option maxHeartbeats 0 in
theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hs : Saved s₀ s.mem)
    (hesi : s.gpr .esi = bp s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .ebx = s₀.gpr .ebx ∧ s'.gpr .esi = s₀.gpr .esi ∧
      s'.gpr .edi = s₀.gpr .edi ∧ ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r := by
  have e64 : (bp s₀ + BitVec.ofNat 32 64).setWidth 64 = BA s₀ + BitVec.ofNat 64 64 := hp.eaB (by omega)
  have e68 : (bp s₀ + BitVec.ofNat 32 68).setWidth 64 = BA s₀ + BitVec.ofNat 64 68 := hp.eaB (by omega)
  have e72 : (bp s₀ + BitVec.ofNat 32 72).setWidth 64 = BA s₀ + BitVec.ofNat 64 72 := hp.eaB (by omega)
  have i64 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 64) 4 := by
    rw [hwr]; exact hp.in_buf (by omega) _
  have i68 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 68) 4 := by
    rw [hwr]; exact hp.in_buf (by omega) _
  have i72 : InRegions (s.rd ++ s.wr) (BA s₀ + BitVec.ofNat 64 72) 4 := by
    rw [hwr]; exact hp.in_buf (by omega) _
  obtain ⟨g1, g2, g3⟩ := hs
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restore, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg,
    State.ea, at_, State.load32, hesi, e64, e68, e72, i64, i68, i72, g1, g2, g3, ite_true,
    ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4]⟩

/-! ## The whole function -/

theorem finish_split : finish ++ restore = (List.range 16).flatMap addWord ++ restore := rfl

theorem block_post {p : Addr} {m : Mem} {R v : CState}
    (h : ∀ j (hj : j < 16), m.readW (wordAddr p j) 32 = R[j] + v[j]) :
    stateAt m p = Vector.zipWith (· + ·) R v := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_zipWith]
  exact h j hj

set_option maxHeartbeats 400000 in
theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa block s₀ fun s' => abiPreserved s₀ s' ∧ Spec.ChaCha20.blockX86.post s₀ s' := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hp) fun s₁ ⟨hk₁, hesi₁, hedi₁, hrd₁, hwr₁, hm₁⟩ => ?_
  have hc₀ : CI s₀ s₁ 0 s₁ :=
    ⟨fun _ _ => rfl, hrd₁, hwr₁, hm₁ ▸ saveMem_frame s₀, Frame.refl _ _,
      fun _ _ h => absurd h (by omega)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (CI s₀ s₁)
    (fun k s hk hc => copy_step hp hesi₁ hedi₁ hk hc) 16 le_rfl s₁ hc₀) fun s₂ hc => ?_
  have hsi₂ : s₂.gpr .esi = bp s₀ := (hc.keep _ (by decide)).trans hesi₁
  have hdi₂ : s₂.gpr .edi = st s₀ := (hc.keep _ (by decide)).trans hedi₁
  have hctx : Ctx (BA s₀) s₂ :=
    ⟨fun k hk => by rw [hsi₂]; exact hp.eaB (by omega),
      fun k hk => by rw [hc.wr]; exact hp.in_buf (by omega) _,
      fun k hk => by rw [hc.wr]; exact hp.out_buf (by omega)⟩
  refine WP.seq (WP.mono (rounds_ok hctx (fun k hk => hc.copied k hk hk) 10) fun s₃ hR => ?_)
  rw [finish_split, WP.block_append_iff]
  have ha₀ : AI s₀ s₃ 0 s₃ :=
    ⟨fun j hj => by simp only [Nat.not_lt_zero, ite_false]; exact hR.holds j hj, fun _ _ => rfl,
      hR.rd.trans hc.rd, hR.wr.trans hc.wr, hc.fb.trans (frame_buf hR.frame), Frame.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (AI s₀ s₃)
    (fun k s hk ha => add_step hp (hR.esi.trans hsi₂) (hR.edi.trans hdi₂) hk ha) 16 le_rfl s₃ ha₀)
    fun s₄ hA => ?_
  have hwork : Frame [workR (BA s₀)] s₁.mem s₄.mem := (hc.fw.trans hR.frame).trans hA.fw
  have hsaved : Saved s₀ s₄.mem := saved_frame (hm₁ ▸ saveMem_saved s₀) hwork
  have hsi₄ : s₄.gpr .esi = bp s₀ := (hA.keep _ (by decide)).trans (hR.esi.trans hsi₂)
  refine WP.mono (restore_ok hp hsaved hsi₄ hA.wr) fun s' ⟨hm', hbx, hsi, hdi, hk'⟩ => ?_
  have hesp : s'.gpr .esp = s₀.gpr .esp := by
    rw [hk' _ (by decide) (by decide) (by decide) (by decide), hA.keep _ (by decide), hR.esp,
      hc.keep _ (by decide), hk₁ _ (by decide) (by decide) (by decide) (by decide)]
  have hebp : s'.gpr .ebp = s₀.gpr .ebp := by
    rw [hk' _ (by decide) (by decide) (by decide) (by decide), hA.keep _ (by decide), hR.ebp,
      hc.keep _ (by decide), hk₁ _ (by decide) (by decide) (by decide) (by decide)]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hbx
    · exact hsi
    · exact hdi
    · exact hebp
    · exact hesp
  · rw [hm']
    refine hA.fb.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    simpa using hp.ret_buf
  · show stateAt s'.mem (BA s₀) = Spec.ChaCha20.block (V s₀)
    rw [hm']
    exact block_post fun j hj => by simpa [hj] using hA.out j hj

/-- Memory whose two argument slots (at `0x4004`) hold `0x1000` and `0x2000`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1000, 64⟩, ⟨0x4004, 8⟩]
  wr := [⟨0x2000, 256⟩]

theorem sat_pre : Spec.ChaCha20.blockX86.pre satState := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x2000 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  simp only [Spec.ChaCha20.blockX86, a0, a1, e]
  refine ⟨by decide, rfl, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, satState] at h₁ h₂
    bv_omega

/-! ## Constant time -/

/-- The initial taint: `esp` is public, and so are the 12 bytes above it (the
return address and the two pointer arguments), which no store changes. -/
def τ₀ : VG.X86.Taint.T := { regs := [.esp], flags := false, argLen := 12 }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hs := hp.esp_fits
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hs, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
  simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  exact VG.X86.Taint.frame_disjoint (n := 8) (by omega) (by simpa using hp.ret_buf)
    (by simpa [argR, argAddr, addr] using hp.arg_buf)

theorem agree₀ {s₁ s₂ : State} (h₁ : Spec.ChaCha20.blockX86.pre s₁)
    (h₂ : Spec.ChaCha20.blockX86.pre s₂) (hpub : Spec.ChaCha20.blockX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  have f₁ : (s₁.gpr .esp).toNat + 12 ≤ 2 ^ 32 := hp₁.esp_fits
  have f₂ : (s₂.gpr .esp).toNat + 12 ≤ 2 ^ 32 := hp₂.esp_fits
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · simp only [τ₀] at hk
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

theorem block_verified :
    Verified X86.target Impl.ChaCha20.X86.block Spec.ChaCha20.blockX86 :=
  ⟨fun s hs => correct (pre_of s hs),
    VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨satState, sat_pre⟩⟩

end VG.Proof.ChaCha20.X86
