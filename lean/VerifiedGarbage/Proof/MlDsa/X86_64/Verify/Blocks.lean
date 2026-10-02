import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.HashCT

/-!
# ML-DSA verification on x86-64: the blocks between the calls

A byte store (`setB_ok`), a copy (`copy_ok`), the mask of a sampler's output
by its result (`mask_ok`: unchanged if 1, zero if 0), and the updates of the
result in `r15` (`and15_ok`, `mov15_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlKem.X86_64 (at_)
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## A byte -/

theorem b8_ofNat {v : Nat} (_hv : v < 256) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.ofNat 32 v)) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem setB_ok (p : Ptr) (v : Nat) (hr : p.1 ≠ .rax) (hv : v < 256) (s : State)
    (hw : InRegions s.wr (pa s p) 1) :
    WP isa (.block (setB p v)) s fun s' =>
      s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 8 v) ∧ Keep [.rax] s s' := by
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 8 v)) ?_ (by rfl))
    fun s' ⟨h, k⟩ => ⟨h, k⟩
  unfold setB
  have e : s.ea (at_ p.1 p.2) = pa s p := ea_at s p.1 p.2
  xrun [hw, hr, b8_ofNat hv, e]

/-! ## A copy -/

theorem b8b (x : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega

theorem copyBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1) (h1 : InRegions s.wr (s.gpr .rdi) 1) :
    WP isa (.block [.movzx8 .rax (at_ .rsi 0), .store8 (at_ .rdi 0) .rax, .alu .add .rdi (.imm 1),
      .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (s.mem (s.gpr .rsi)) ∧ s'.gpr .rdi = s.gpr .rdi + 1 ∧
        s'.gpr .rsi = s.gpr .rsi + 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdi, .rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h0, h1, b8b]

theorem inRegions_byte {rs : List Region} {a : Addr} {n k : Nat} (h : InRegions rs a n) (hk : k < n)
    (hn : n < 2 ^ 64) : InRegions rs (a + BitVec.ofNat 64 k) 1 := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat a (by omega)]; exact hk)⟩

abbrev copyArgs (dst src : Ptr) (n : Nat) : List (Reg × Arg) := [(.rdi, .ptr dst), (.rsi, .ptr src), (.rcx, .imm n)]

theorem copy_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {dst src : Ptr} {n : Nat}
    (hn0 : 0 < n) (hsd : sepB (rbs ++ wbs) src n dst n = true) (hw : inB wbs dst n = true) :
    WP isa (copy dst src n) s fun s' => PPostB s s' [(dst, n)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (pa s dst) n = bytesAt s.mem (pa s src) n := by
  have hsd' := sepB_spec hsd
  have hS := L.ok
  have hn : n < 2 ^ 31 := by
    obtain ⟨m, hm, hl⟩ := inB_spec hsd'.1; have := (hS _ hm).1; omega
  have hok : ∀ a ∈ copyArgs dst src n, a.2.Ok ∧ a.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨ptr_ok hS hsd'.2.1, by decide⟩, ⟨ptr_ok hS hsd'.1, by decide⟩, ⟨hn, by decide⟩⟩
  have hrd := L.inR hsd'.1
  have hwr := L.inW hw
  have hdj := L.disj hsd
  unfold copy
  refine WP.seq (WP.mono (glue_ok' hok (by simp only [List.map_cons, List.map_nil]; decide) s)
    fun s1 (h1 : Args (copyArgs dst src n) s s1) => ?_)
  refine WP.mono (wp_countdown (cnt := .rcx) (N := n) (by omega) hn0 (fun k s' =>
      s'.gpr .rdi = pa s dst + BitVec.ofNat 64 k ∧ s'.gpr .rsi = pa s src + BitVec.ofNat 64 k ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨pa s dst, n⟩] s.mem s'.mem ∧
      (∀ j < k, s'.mem (pa s dst + BitVec.ofNat 64 j) = s.mem (pa s src + BitVec.ofNat 64 j)) ∧
      Keep argRegs s s')
    (fun k hk s' ⟨hdi, hsi, hrd', hwr', hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [h1.r0]; simp [Arg.val], by rw [h1.r1]; simp [Arg.val], h1.2.2.1, h1.2.2.2,
      by rw [h1.1.2]; exact Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _), h1.2⟩ (by rw [h1.r2]; rfl))
    fun s' ⟨_, _, _, _, hf, hc, kk⟩ => ⟨postB_of_keep kk (by decide) (by simpa using hf), kk.gpr (by decide), ?_⟩
  · refine WP.mono (copyBody_ok s' (by rw [hrd', hwr', hsi]; exact inRegions_byte hrd hk (by omega))
      (by rw [hwr', hdi]; exact inRegions_byte hwr hk (by omega))) fun s'' ⟨⟨hm, hdi', hsi', hcx, hz⟩, k'⟩ =>
        ⟨⟨by rw [hdi', hdi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, BitVec.ofNat_add],
          by rw [hsi', hsi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, BitVec.ofNat_add],
          k'.2.1.trans hrd', k'.2.2.trans hwr', ?_, fun j hj => ?_, (kk.trans k').mono (by decide)⟩, hcx, hz⟩
    · rw [hm, hdi]
      exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega) (by omega))
    · have hsrc : s'.mem (pa s src + BitVec.ofNat 64 k) = s.mem (pa s src + BitVec.ofNat 64 k) :=
        hf.bytes (R := ⟨pa s src, n⟩) (by simpa using hdj) (show n ≤ 2 ^ 64 by omega) hk
      rw [hm, hdi, hsi, VG.WriteBytes.writeW8_apply]
      by_cases e : j = k
      · subst e; rw [ifp rfl, hsrc]
      · rw [ifn (fun h => e (by have := congrArg BitVec.toNat h; simp at this; omega)), hc j (by omega)]
  · simp only [bytesAt]
    exact List.map_congr_left fun i hi => hc i (List.mem_range.mp hi)


/-! ## The mask -/

theorem maskPre_ok (s : State) :
    WP isa (.block [.mov32 .rdx (.imm 0), .alu32 .sub .rdx (.reg .rax)]) s fun s' =>
      (s'.mem = s.mem ∧ (s'.gpr .rdx).setWidth 32 = 0 - (s.gpr .rax).setWidth 32) ∧ Keep [.rdx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem maskBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4) (h1 : InRegions s.wr (s.gpr .rdi) 4) :
    WP isa (.block [.mov32 .rax (.mem (at_ .rdi 0)), .alu32 .and .rax (.reg .rdx), .store32 (at_ .rdi 0) .rax,
      .alu .add .rdi (.imm 4), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (s.mem.readW (s.gpr .rdi) 32 &&& (s.gpr .rdx).setWidth 32) ∧
        s'.gpr .rdi = s.gpr .rdi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.gpr .rdx = s.gpr .rdx ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h0, h1]

theorem coeffAt_writeW' (m : Mem) (p : Addr) {N i j : Nat} (hN : 4 * N ≤ 2 ^ 64) (hi : i < N) (hj : j < N)
    (v : BitVec 32) :
    coeffAt (m.writeW (p + BitVec.ofNat 64 (4 * j)) v) p i = if j = i then v else coeffAt m p i := by
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- The mask of the `N` coefficients from `a` by `eax`: each `∧ -eax`. -/
theorem maskN_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {a : Ptr} {N : Nat} (hN0 : 0 < N)
    (hN : N < 2 ^ 29) (hi : inB (rbs ++ wbs) a (4 * N) = true) (hw : inB wbs a (4 * N) = true) :
    WP isa (mask a N) s fun s' => PPostB s s' [(a, 4 * N)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      ∀ i < N, coeffAt s'.mem (pa s a) i = coeffAt s.mem (pa s a) i &&& (0 - (s.gpr .rax).setWidth 32) := by
  have hS := L.ok
  have hok : ∀ x ∈ ([(.rdi, .ptr a), (.rcx, .imm N)] : List (Reg × Arg)), x.2.Ok ∧ x.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨ptr_ok hS hi, by decide⟩, ⟨show N < 2 ^ 31 by omega, by decide⟩⟩
  have hrd := L.inR hi
  have hwr := L.inW hw
  unfold mask
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (maskPre_ok s) fun s₀ ⟨⟨hm₀, hd₀⟩, k₀⟩ => ?_
  refine WP.mono (glue_ok _ hok (by simp only [List.map_cons, List.map_nil]; decide) s₀)
    fun s1 ⟨⟨hv1, hm1⟩, k1⟩ => ?_
  have hb := ptr_bs hS hi
  have nb : a.1 ∉ [Reg.rdx] := by
    simp only [List.mem_singleton]; intro h; rw [h] at hb; exact absurd hb (by decide)
  have e1 : s1.gpr .rdi = pa s a := by
    rw [hv1 _ (List.mem_cons_self ..)]; simp only [Arg.val, pa]; rw [k₀.gpr nb]
  have e2 : s1.gpr .rcx = BitVec.ofNat 64 N := hv1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hd1 : (s1.gpr .rdx).setWidth 32 = 0 - (s.gpr .rax).setWidth 32 := by rw [k1.gpr (by simp), hd₀]
  have k01 : Keep [.rdx, .rdi, .rcx] s s1 := (k₀.trans k1).mono (by simp)
  have hm01 : s1.mem = s.mem := hm1.trans hm₀
  refine WP.mono (wp_countdown (cnt := .rcx) (N := N) (by omega) hN0 (fun k s' =>
      s'.gpr .rdi = pa s a + BitVec.ofNat 64 (4 * k) ∧ (s'.gpr .rdx).setWidth 32 = 0 - (s.gpr .rax).setWidth 32 ∧
      Frame [⟨pa s a, 4 * N⟩] s.mem s'.mem ∧
      (∀ i < N, coeffAt s'.mem (pa s a) i =
        if i < k then coeffAt s.mem (pa s a) i &&& (0 - (s.gpr .rax).setWidth 32) else coeffAt s.mem (pa s a) i) ∧
      Keep [.rdx, .rdi, .rcx, .rax] s s')
    (fun k hk s' ⟨hdi, hdx, hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [e1]; simp, hd1, by rw [hm01]; exact Frame.refl _ _, fun i _ => by rw [hm01, ifn (Nat.not_lt_zero _)],
      k01.mono (by simp)⟩ e2)
    fun s' ⟨_, _, hf, hc, kk⟩ => ⟨postB_of_keep kk (by decide) (by simpa using hf),
      kk.gpr (by decide), fun i hi => by rw [hc i hi, ifp hi]⟩
  refine WP.mono (maskBody_ok s' (by rw [kk.2.1, kk.2.2, hdi]; exact inRegions_sub hrd (by omega) (by omega))
      (by rw [kk.2.2, hdi]; exact inRegions_sub hwr (by omega) (by omega)))
    fun s'' ⟨⟨hm, hdi', hcx, hdx', hz⟩, k'⟩ => ⟨⟨?_, by rw [hdx', hdx], ?_, fun i hi => ?_,
      (kk.trans k').mono (by simp)⟩, hcx, hz⟩
  · rw [hdi', hdi, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 * k + 4 = 4 * (k + 1) by omega]
  · rw [hm, hdi]
    exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega) (by omega))
  · have hck : s'.mem.readW (pa s a + BitVec.ofNat 64 (4 * k)) 32 = coeffAt s.mem (pa s a) k := by
      have := hc k (by omega)
      rw [ifn (Nat.lt_irrefl _)] at this
      exact this
    rw [hm, hdi, hck, hdx, coeffAt_writeW' _ _ (N := N) (by omega) hi (by omega)]
    by_cases e : k = i
    · subst e; rw [ifp rfl, ifp (Nat.lt_succ_self _)]
    · rw [ifn e, hc i hi]
      by_cases h' : i < k
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]

/-- The mask of the polynomial at `a` by `eax`: each coefficient `∧ -eax`. -/
theorem mask_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {a : Ptr}
    (hi : inB (rbs ++ wbs) a 1024 = true) (hw : inB wbs a 1024 = true) :
    WP isa (mask a) s fun s' => PPostB s s' [(a, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      ∀ i < n, coeffAt s'.mem (pa s a) i = coeffAt s.mem (pa s a) i &&& (0 - (s.gpr .rax).setWidth 32) :=
  maskN_ok L (N := 256) (by decide) (by decide) hi hw

end VG.Proof.MlDsa.X86_64.Verify
