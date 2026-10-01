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

end VG.Proof.Aes.X86.AesNi
