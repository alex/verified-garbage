import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyContext

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (EPre keyP keyLen keyR ekSchP ekSchR)
open VG.Impl.Aes.X86.AesNi (at_ rc kstep kstepB6 expand128 expand192 expand256)

/-- The stored schedule prefix and unchanged entry pointers. -/
structure KeyBody (s₀ entry : State) (nk K : Nat) (s : State) : Prop where
  words : Good s.mem ((ekSchP s₀).setWidth 64) (W s₀.mem ((keyP s₀).setWidth 64) nk) K
  gpr : s.gpr = entry.gpr
  rd : s.rd = entry.rd
  wr : s.wr = entry.wr
  frame : Frame [ekSchR s₀] s₀.mem s.mem

theorem KeyBody.initial {s₀ entry : State} (hs : KeyReady s₀ entry) (nk : Nat) :
    KeyBody s₀ entry nk 0 entry :=
  ⟨fun i hi => False.elim (by omega), rfl, rfl, rfl, by rw [hs.mem]; exact Frame.refl _ _⟩

theorem KeyBody.ea {s₀ entry s : State} {nk K d : Nat} (hp : EPre s₀)
    (hs : KeyReady s₀ entry) (h : KeyBody s₀ entry nk K s) (hd : d < 240) :
    s.ea (at_ .edx d) = (ekSchP s₀).setWidth 64 + BitVec.ofNat 64 d := by
  change addr (s.gpr .edx) d = _
  rw [h.gpr, hs.edx, addr_eq (by have hf := hp.fS; omega)]

theorem KeyBody.writable {s₀ entry s : State} {nk K d : Nat} (hp : EPre s₀)
    (hs : KeyReady s₀ entry) (h : KeyBody s₀ entry nk K s) (hd : d + 16 ≤ 240) :
    InRegions s.wr (s.ea (at_ .edx d)) 16 := by
  rw [h.ea hp hs (by omega), h.wr, hs.wr]
  exact ⟨ekSchR s₀, by simp only [hp.wr, List.mem_cons, true_or],
    Offset.contains_base _ hd (by omega)⟩

theorem KeyBody.stored {s₀ entry s : State} {nk K n : Nat} (hp : EPre s₀)
    (hs : KeyReady s₀ entry) (h : KeyBody s₀ entry nk K s) (v : BitVec 128)
    (hn : n ≤ 4) (hv : ∀ j < n, dword v j = W s₀.mem ((keyP s₀).setWidth 64) nk (K + j))
    (hK : 4 * K + 16 ≤ 240) {s' : State}
    (mem : s'.mem = s.mem.writeW (s.ea (at_ .edx (4 * K))) v)
    (gpr : s'.gpr = s.gpr) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) :
    KeyBody s₀ entry nk (K + n) s' := by
  have ea := h.ea hp hs (d := 4 * K) (by omega)
  refine ⟨?_, gpr.trans h.gpr, rd.trans h.rd, wr.trans h.wr, ?_⟩
  · rw [mem, ea]; exact good_store h.words v hn hv hK
  · rw [mem, ea]
    exact h.frame.writeW (v := v) (List.mem_singleton_self _)
      (Offset.contains_base _ hK (by omega))

theorem key_store_ok {s₀ entry s : State} {nk K n : Nat} (hp : EPre s₀)
    (hs : KeyReady s₀ entry) (h : KeyBody s₀ entry nk K s) (x : XReg)
    (hn : n ≤ 4) (hv : ∀ j < n, dword (s.xmm x) j = W s₀.mem ((keyP s₀).setWidth 64) nk (K + j))
    (hK : 4 * K + 16 ≤ 240) :
    WP isa (.block [.movdquStore (at_ .edx (4 * K)) x]) s fun s' =>
      KeyBody s₀ entry nk (K + n) s' ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  have hw := h.writable hp hs hK
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store128,
    hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨h.stored hp hs _ hn hv hK rfl rfl rfl rfl, trivial⟩

theorem key_step_ok {s₀ entry s : State} {nk K n : Nat} (hp : EPre s₀)
    (hs : KeyReady s₀ entry) (h : KeyBody s₀ entry nk K s)
    (d src : XReg) (sel r : BitVec 8) (hd3 : d ≠ .xmm3) (hd4 : d ≠ .xmm4)
    (hn : n ≤ 4)
    (hv : ∀ j < n, dword (kv (s.xmm d) (shufDwords (aesKeygenAssist (s.xmm src) r) sel)) j =
      W s₀.mem ((keyP s₀).setWidth 64) nk (K + j))
    (hK : 4 * K + 16 ≤ 240) :
    WP isa (.block (kstep d src sel r (4 * K))) s fun s' =>
      KeyBody s₀ entry nk (K + n) s' ∧
      s'.xmm d = kv (s.xmm d) (shufDwords (aesKeygenAssist (s.xmm src) r) sel) ∧
      ∀ x, x ≠ d → x ≠ .xmm3 → x ≠ .xmm4 → s'.xmm x = s.xmm x := by
  refine WP.mono (kstep_exec d src sel r (4 * K) s hd3 hd4 (h.writable hp hs hK))
    fun s' ⟨val, mem, gpr, rd, wr, other⟩ => ?_
  exact ⟨h.stored hp hs _ hn hv hK mem gpr rd wr, val, other⟩


theorem key_load_ok {s₀ entry s : State} {nk K off : Nat} (hp : EPre s₀)
    (hs : KeyReady s₀ entry) (h : KeyBody s₀ entry nk K s) (x : XReg)
    (hoff : off + 16 ≤ keyLen s₀) :
    WP isa (.block [.movdquLoad x (at_ .eax off)]) s fun s' =>
      KeyBody s₀ entry nk K s' ∧
      s'.xmm x = s₀.mem.readW ((keyP s₀).setWidth 64 + BitVec.ofNat 64 off) 128 ∧
      ∀ y, y ≠ x → s'.xmm y = s.xmm y := by
  have ea : s.ea (at_ .eax off) = (keyP s₀).setWidth 64 + BitVec.ofNat 64 off := by
    change addr (s.gpr .eax) off = _
    rw [h.gpr, hs.eax, addr_eq (by have hf := hp.fK; omega)]
  have hc : (keyR s₀).Contains (s.ea (at_ .eax off)) 16 := by
    rw [ea]; exact Offset.contains_base _ hoff (by have hf := hp.fK; omega)
  have hr : InRegions (s.rd ++ s.wr) (s.ea (at_ .eax off)) 16 := by
    refine ⟨keyR s₀, ?_, hc⟩
    simp only [h.rd, hs.rd, hp.rd, List.mem_append, List.mem_cons, true_or]
  have hm : s.mem.readW (s.ea (at_ .eax off)) 128 = s₀.mem.readW (s.ea (at_ .eax off)) 128 := h.frame.readW hc (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r; exact hp.dKS) (by decide)
  apply WP.of_runBlock
  rw [runBlock_cons, key_load_exec s x _ hr, runStep_some, runBlock_nil]
  refine ⟨s.setXmm x _, rfl, ?_⟩
  refine ⟨⟨h.words, h.gpr, h.rd, h.wr, h.frame⟩, ?_, ?_⟩
  · rw [xmm_setXmm_self, hm, ea]
  · intro y hy; exact xmm_setXmm_of_ne _ _ hy

structure KeyInv128 (s₀ entry : State) (k : Nat) (s : State) : Prop extends KeyBody s₀ entry 4 (4 * (k + 1)) s where
  a : ∀ j < 4, dword (s.xmm .xmm1) j = W s₀.mem ((keyP s₀).setWidth 64) 4 (4 * k + j)

theorem key128_step {s₀ entry s : State} (hp : EPre s₀) (hs : KeyReady s₀ entry)
    {k : Nat} (hk : k < 10) (h : KeyInv128 s₀ entry k s) :
    WP isa (.block (kstep .xmm1 .xmm1 0xff (rc (k + 1)) (16 * (k + 1)))) s
      (KeyInv128 s₀ entry (k + 1)) := by
  have hv := key128_next k (s.xmm .xmm1) h.a
  have he : 16 * (k + 1) = 4 * (4 * (k + 1)) := by omega
  rw [he]
  refine WP.mono (key_step_ok hp hs h.toKeyBody .xmm1 .xmm1 0xff (rc (k + 1))
    (by decide) (by decide) (n := 4) (by decide) hv (by omega))
    fun s' ⟨body, val, _⟩ => ?_
  refine ⟨?_, ?_⟩
  · rw [show 4 * (k + 1 + 1) = 4 * (k + 1) + 4 by omega]
    exact body
  · rw [val]; exact hv

theorem key128_rounds {s₀ entry s : State} (hp : EPre s₀) (hs : KeyReady s₀ entry)
    (n : Nat) (hn : n ≤ 10) (h : KeyInv128 s₀ entry 0 s) :
    WP isa (.block ((List.range n).flatMap fun k =>
      kstep .xmm1 .xmm1 0xff (rc (k + 1)) (16 * (k + 1)))) s (KeyInv128 s₀ entry n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (ih (by omega)) fun _ hn' => key128_step hp hs (by omega) hn'

theorem expand128_ok (s₀ entry : State) (hp : EPre s₀) (hs : KeyReady s₀ entry)
    (hlen : keyLen s₀ = 16) : WP isa (.block expand128) entry (KeyDone s₀ entry 4) := by
  unfold expand128
  rw [show ([.movdquLoad .xmm1 (at_ .eax 0), .movdquStore (at_ .edx 0) .xmm1] : List Instr) =
    [.movdquLoad .xmm1 (at_ .eax 0)] ++ [.movdquStore (at_ .edx 0) .xmm1] by rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (key_load_ok hp hs (KeyBody.initial hs 4) .xmm1 (by omega))
    fun s₁ ⟨h₁, a, _⟩ => ?_
  have ha : ∀ j < 4, dword (s₁.xmm .xmm1) j = W s₀.mem ((keyP s₀).setWidth 64) 4 j := by
    have av : s₁.xmm .xmm1 = s₀.mem.readW ((keyP s₀).setWidth 64) 128 := by
      simpa only [BitVec.add_zero] using a
    intro j hj
    rw [av]
    have init := key_initial_words s₀.mem ((keyP s₀).setWidth 64) 4 0 (by decide)
    simp only [Nat.mul_zero, BitVec.add_zero, Nat.zero_add] at init
    exact init j hj
  rw [WP.block_append_iff]
  refine WP.mono (key_store_ok hp hs h₁ .xmm1 (n := 4) (by decide)
    (by simpa only [Nat.zero_add] using ha) (by decide)) fun s₂ ⟨h₂, x₂⟩ => ?_
  have hI : KeyInv128 s₀ entry 0 s₂ := ⟨h₂, by rw [x₂]; simpa only [Nat.mul_zero, Nat.zero_add] using ha⟩
  exact WP.mono (key128_rounds hp hs 10 (by decide) hI) fun _ hfin =>
    ⟨hfin.words, hfin.gpr, hfin.rd, hfin.wr, hfin.frame⟩


theorem key_load_words {s₀ entry s : State} {nk K off : Nat} (hp : EPre s₀)
    (hs : KeyReady s₀ entry) (h : KeyBody s₀ entry nk K s) (x : XReg)
    (hoff : off + 4 ≤ nk) (hlen : keyLen s₀ = 4 * nk) :
    WP isa (.block [.movdquLoad x (at_ .eax (4 * off))]) s fun s' =>
      KeyBody s₀ entry nk K s' ∧
      (∀ j < 4, dword (s'.xmm x) j = W s₀.mem ((keyP s₀).setWidth 64) nk (off + j)) ∧
      ∀ y, y ≠ x → s'.xmm y = s.xmm y := by
  refine WP.mono (key_load_ok hp hs h x (by omega)) fun s' ⟨body, val, other⟩ => ?_
  refine ⟨body, ?_, other⟩
  intro j hj
  rw [val]
  exact key_initial_words _ _ nk off hoff j hj

structure KeyInv256 (s₀ entry : State) (k : Nat) (s : State) : Prop extends KeyBody s₀ entry 8 (8 * (k + 1)) s where
  a : ∀ j < 4, dword (s.xmm .xmm1) j = W s₀.mem ((keyP s₀).setWidth 64) 8 (8 * k + j)
  b : ∀ j < 4, dword (s.xmm .xmm2) j = W s₀.mem ((keyP s₀).setWidth 64) 8 (8 * k + 4 + j)

def key256_pair (k : Nat) : List Instr :=
  kstep .xmm1 .xmm2 0xff (rc (k + 1)) (32 * (k + 1)) ++
    kstep .xmm2 .xmm1 0xaa 0 (32 * (k + 1) + 16)

theorem key256_step {s₀ entry s : State} (hp : EPre s₀) (hs : KeyReady s₀ entry)
    {k : Nat} (hk : k < 6) (h : KeyInv256 s₀ entry k s) :
    WP isa (.block (key256_pair k)) s (KeyInv256 s₀ entry (k + 1)) := by
  unfold key256_pair
  rw [WP.block_append_iff, show 32 * (k + 1) = 4 * (8 * (k + 1)) by omega]
  have hv := key256_first k (s.xmm .xmm1) (s.xmm .xmm2) h.a h.b
  refine WP.mono (key_step_ok hp hs h.toKeyBody .xmm1 .xmm2 0xff (rc (k + 1))
    (by decide) (by decide) (n := 4) (by decide) hv (by omega))
    fun s₁ ⟨h₁, a₁, oth₁⟩ => ?_
  have ha : ∀ j < 4, dword (s₁.xmm .xmm1) j = W s₀.mem ((keyP s₀).setWidth 64) 8 (8 * (k + 1) + j) := by
    rw [a₁]; exact hv
  have hb : ∀ j < 4, dword (s₁.xmm .xmm2) j = W s₀.mem ((keyP s₀).setWidth 64) 8 (8 * k + 4 + j) := by
    rw [oth₁ .xmm2 (by decide) (by decide) (by decide)]; exact h.b
  have hv₂ := key256_second k (s₁.xmm .xmm1) (s₁.xmm .xmm2) ha hb
  rw [show 4 * (8 * (k + 1)) + 16 = 4 * (8 * (k + 1) + 4) by omega]
  refine WP.mono (key_step_ok hp hs h₁ .xmm2 .xmm1 0xaa 0
    (by decide) (by decide) (n := 4) (by decide) hv₂ (by omega))
    fun s₂ ⟨h₂, b₂, oth₂⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [show 8 * (k + 1 + 1) = 8 * (k + 1) + 4 + 4 by omega]; exact h₂
  · rw [oth₂ .xmm1 (by decide) (by decide) (by decide)]; exact ha
  · rw [b₂]; exact hv₂

theorem key256_rounds {s₀ entry s : State} (hp : EPre s₀) (hs : KeyReady s₀ entry)
    (n : Nat) (hn : n ≤ 6) (h : KeyInv256 s₀ entry 0 s) :
    WP isa (.block ((List.range n).flatMap key256_pair)) s (KeyInv256 s₀ entry n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (ih (by omega)) fun _ hn' => key256_step hp hs (by omega) hn'

theorem key256_last {s₀ entry s : State} (hp : EPre s₀) (hs : KeyReady s₀ entry)
    (h : KeyInv256 s₀ entry 6 s) :
    WP isa (.block (kstep .xmm1 .xmm2 0xff (rc 7) 224)) s (KeyDone s₀ entry 8) := by
  have hv := key256_first 6 (s.xmm .xmm1) (s.xmm .xmm2) h.a h.b
  exact WP.mono (key_step_ok hp hs h.toKeyBody .xmm1 .xmm2 0xff (rc 7)
    (by decide) (by decide) (n := 4) (by decide) hv (by decide))
    fun _ ⟨hf, _, _⟩ => ⟨hf.words, hf.gpr, hf.rd, hf.wr, hf.frame⟩

/-- Initial AES-256 key lanes are loaded before any schedule stores. -/
theorem key256_initial (s₀ entry : State) (hp : EPre s₀) (hs : KeyReady s₀ entry)
    (hlen : keyLen s₀ = 32) :
    WP isa (.block [.movdquLoad .xmm1 (at_ .eax 0), .movdquLoad .xmm2 (at_ .eax 16),
      .movdquStore (at_ .edx 0) .xmm1, .movdquStore (at_ .edx 16) .xmm2]) entry (KeyInv256 s₀ entry 0) := by
  change WP isa (.block (([.movdquLoad .xmm1 (at_ .eax (4 * 0))] : List Instr) ++
    ([.movdquLoad .xmm2 (at_ .eax (4 * 4))] : List Instr) ++
    ([.movdquStore (at_ .edx 0) .xmm1] : List Instr) ++
    ([.movdquStore (at_ .edx 16) .xmm2] : List Instr))) entry _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (key_load_words hp hs (KeyBody.initial hs 8) .xmm1 (off := 0) (by decide) hlen)
    fun s₁ ⟨h₁, a₁, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (key_load_words hp hs h₁ .xmm2 (off := 4) (by decide) hlen)
    fun s₂ ⟨h₂, b₂, oth₂⟩ => ?_
  have ha : ∀ j < 4, dword (s₂.xmm .xmm1) j = W s₀.mem ((keyP s₀).setWidth 64) 8 j := by
    rw [oth₂ .xmm1 (by decide)]; simpa only [Nat.zero_add] using a₁
  rw [WP.block_append_iff]
  refine WP.mono (key_store_ok hp hs h₂ .xmm1 (n := 4) (by decide) (by simpa only [Nat.zero_add] using ha) (by decide))
    fun s₃ ⟨h₃, x₃⟩ => ?_
  refine WP.mono (key_store_ok hp hs h₃ .xmm2 (n := 4) (by decide)
    (by rw [x₃]; exact b₂) (by decide)) fun s₄ ⟨h₄, x₄⟩ => ?_
  refine ⟨h₄, ?_, ?_⟩
  · rw [x₄, x₃]; simpa only [Nat.mul_zero, Nat.zero_add] using ha
  · rw [x₄, x₃]; simpa only [Nat.mul_zero, Nat.zero_add] using b₂

theorem expand256_ok (s₀ entry : State) (hp : EPre s₀) (hs : KeyReady s₀ entry)
    (hlen : keyLen s₀ = 32) : WP isa (.block expand256) entry (KeyDone s₀ entry 8) := by
  unfold expand256
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (key256_initial s₀ entry hp hs hlen) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  exact WP.mono (key256_rounds hp hs 6 (by decide) h₁) fun _ hfin => key256_last hp hs hfin


structure KeyInv192 (s₀ entry : State) (k : Nat) (s : State) : Prop extends KeyBody s₀ entry 6 (6 * (k + 1)) s where
  a : ∀ j < 4, dword (s.xmm .xmm1) j = W s₀.mem ((keyP s₀).setWidth 64) 6 (6 * k + j)
  b : ∀ j < 2, dword (s.xmm .xmm2) j = W s₀.mem ((keyP s₀).setWidth 64) 6 (6 * k + 4 + j)

def key192_pair (k : Nat) : List Instr :=
  kstep .xmm1 .xmm2 0x55 (rc (k + 1)) (24 * (k + 1)) ++ kstepB6 (24 * (k + 1) + 16)

theorem key192_step {s₀ entry s : State} (hp : EPre s₀) (hs : KeyReady s₀ entry)
    {k : Nat} (hk : k < 7) (h : KeyInv192 s₀ entry k s) :
    WP isa (.block (key192_pair k)) s (KeyInv192 s₀ entry (k + 1)) := by
  unfold key192_pair
  rw [WP.block_append_iff, show 24 * (k + 1) = 4 * (6 * (k + 1)) by omega]
  have hv := key192_first k (s.xmm .xmm1) (s.xmm .xmm2) h.a h.b
  refine WP.mono (key_step_ok hp hs h.toKeyBody .xmm1 .xmm2 0x55 (rc (k + 1))
    (by decide) (by decide) (n := 4) (by decide) hv (by omega))
    fun s₁ ⟨h₁, a₁, oth₁⟩ => ?_
  have ha : ∀ j < 4, dword (s₁.xmm .xmm1) j = W s₀.mem ((keyP s₀).setWidth 64) 6 (6 * (k + 1) + j) := by
    rw [a₁]; exact hv
  have hb : ∀ j < 2, dword (s₁.xmm .xmm2) j = W s₀.mem ((keyP s₀).setWidth 64) 6 (6 * k + 4 + j) := by
    rw [oth₁ .xmm2 (by decide) (by decide) (by decide)]; exact h.b
  have hv₂ := key192_second k (s₁.xmm .xmm1) (s₁.xmm .xmm2) ha hb
  rw [show 4 * (6 * (k + 1)) + 16 = 4 * (6 * (k + 1) + 4) by omega]
  have hK : 4 * (6 * (k + 1) + 4) + 16 ≤ 240 := by omega
  refine WP.mono (kstepB6_exec (4 * (6 * (k + 1) + 4)) s₁ (h₁.writable hp hs hK))
    fun s₂ ⟨b₂, mem, gpr, rd, wr, oth₂⟩ => ?_
  have h₂ := h₁.stored hp hs _ (n := 2) (by decide) hv₂ hK mem gpr rd wr
  refine ⟨?_, ?_, ?_⟩
  · rw [show 6 * (k + 1 + 1) = 6 * (k + 1) + 4 + 2 by omega]; exact h₂
  · rw [oth₂ .xmm1 (by decide) (by decide) (by decide)]; exact ha
  · rw [b₂]; exact hv₂

theorem key192_rounds {s₀ entry s : State} (hp : EPre s₀) (hs : KeyReady s₀ entry)
    (n : Nat) (hn : n ≤ 7) (h : KeyInv192 s₀ entry 0 s) :
    WP isa (.block ((List.range n).flatMap key192_pair)) s (KeyInv192 s₀ entry n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (ih (by omega)) fun _ hn' => key192_step hp hs (by omega) hn'

theorem key192_last {s₀ entry s : State} (hp : EPre s₀) (hs : KeyReady s₀ entry)
    (h : KeyInv192 s₀ entry 7 s) :
    WP isa (.block (kstep .xmm1 .xmm2 0x55 (rc 8) 192)) s (KeyDone s₀ entry 6) := by
  have hv := key192_first 7 (s.xmm .xmm1) (s.xmm .xmm2) h.a h.b
  exact WP.mono (key_step_ok hp hs h.toKeyBody .xmm1 .xmm2 0x55 (rc 8)
    (by decide) (by decide) (n := 4) (by decide) hv (by decide))
    fun _ ⟨hf, _, _⟩ => ⟨hf.words, hf.gpr, hf.rd, hf.wr, hf.frame⟩

/-- The upper two key words are moved into the low two SIMD lanes. -/
theorem dword_psrldq8 (v : BitVec 128) (j : Nat) :
    dword (XShiftOp.eval .psrldq v 8) j = dword v (j + 2) := by
  change dword (v >>> 64) j = _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  exact congrArg _ (by omega)

theorem key192_shift {s₀ entry s : State} (h : KeyBody s₀ entry 6 0 s)
    (ha : ∀ j < 4, dword (s.xmm .xmm1) j = W s₀.mem ((keyP s₀).setWidth 64) 6 j)
    (hb : ∀ j < 4, dword (s.xmm .xmm2) j = W s₀.mem ((keyP s₀).setWidth 64) 6 (2 + j)) :
    WP isa (.block [.xop (.shift .psrldq .xmm2 8)]) s fun s' =>
      KeyBody s₀ entry 6 0 s' ∧
      (∀ j < 4, dword (s'.xmm .xmm1) j = W s₀.mem ((keyP s₀).setWidth 64) 6 j) ∧
      ∀ j < 2, dword (s'.xmm .xmm2) j = W s₀.mem ((keyP s₀).setWidth 64) 6 (4 + j) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨h.words, h.gpr, h.rd, h.wr, h.frame⟩, ?_, ?_⟩
  · rw [xmm_setXmm_of_ne _ _ (by decide)]; exact ha
  · intro j hj
    rw [xmm_setXmm_self, dword_psrldq8 _ j, hb (j + 2) (by omega),
      show 2 + (j + 2) = 4 + j by omega]

theorem key192_initial (s₀ entry : State) (hp : EPre s₀) (hs : KeyReady s₀ entry)
    (hlen : keyLen s₀ = 24) :
    WP isa (.block [.movdquLoad .xmm1 (at_ .eax 0), .movdquLoad .xmm2 (at_ .eax 8),
      .xop (.shift .psrldq .xmm2 8), .movdquStore (at_ .edx 0) .xmm1,
      .movdquStore (at_ .edx 16) .xmm2]) entry (KeyInv192 s₀ entry 0) := by
  change WP isa (.block (([.movdquLoad .xmm1 (at_ .eax (4 * 0))] : List Instr) ++
    ([.movdquLoad .xmm2 (at_ .eax (4 * 2))] : List Instr) ++
    ([.xop (.shift .psrldq .xmm2 8)] : List Instr) ++
    ([.movdquStore (at_ .edx 0) .xmm1] : List Instr) ++
    ([.movdquStore (at_ .edx 16) .xmm2] : List Instr))) entry _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (key_load_words hp hs (KeyBody.initial hs 6) .xmm1 (off := 0) (by decide) hlen)
    fun s₁ ⟨h₁, a₁, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (key_load_words hp hs h₁ .xmm2 (off := 2) (by decide) hlen)
    fun s₂ ⟨h₂, b₂, oth₂⟩ => ?_
  have ha : ∀ j < 4, dword (s₂.xmm .xmm1) j = W s₀.mem ((keyP s₀).setWidth 64) 6 j := by
    rw [oth₂ .xmm1 (by decide)]; simpa only [Nat.zero_add] using a₁
  rw [WP.block_append_iff]
  refine WP.mono (key192_shift h₂ ha b₂) fun s₃ ⟨h₃, a₃, b₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (key_store_ok hp hs h₃ .xmm1 (n := 4) (by decide)
    (by simpa only [Nat.zero_add] using a₃) (by decide)) fun s₄ ⟨h₄, x₄⟩ => ?_
  refine WP.mono (key_store_ok hp hs h₄ .xmm2 (n := 2) (by decide)
    (by rw [x₄]; exact b₃) (by decide)) fun s₅ ⟨h₅, x₅⟩ => ?_
  refine ⟨h₅, ?_, ?_⟩
  · rw [x₅, x₄]; simpa only [Nat.mul_zero, Nat.zero_add] using a₃
  · rw [x₅, x₄]; simpa only [Nat.mul_zero, Nat.zero_add] using b₃

theorem expand192_ok (s₀ entry : State) (hp : EPre s₀) (hs : KeyReady s₀ entry)
    (hlen : keyLen s₀ = 24) : WP isa (.block expand192) entry (KeyDone s₀ entry 6) := by
  unfold expand192
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (key192_initial s₀ entry hp hs hlen) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  exact WP.mono (key192_rounds hp hs 7 (by decide) h₁) fun _ hfin => key192_last hp hs hfin

end VG.Proof.Aes.X86.AesNi
