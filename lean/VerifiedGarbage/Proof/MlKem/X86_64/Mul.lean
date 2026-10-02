import VerifiedGarbage.Proof.MlKem.X86_64.VMul
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86-64: `vg_mlkem_multiply_ntts`

Each iteration of the loop loads 16 coefficients of `f` and of `g` into the
words of their pairs (`deintF_ok`, `deintG_ok`), multiplies the eight pairs
(`vbase_ok`) and stores the 16 coefficients of `h` (`vinter_ok`): `Mul.step`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- `vg_mlkem_multiply_ntts(h = rdi, f = rsi, g = rdx, scratch = rcx)`. -/
def mulK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi), pR (s.gpr .rdx)] ∧ s.wr = [pR (s.gpr .rdi), pR (s.gpr .rcx)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rcx)) ∧
    (pR (s.gpr .rdx)).Disjoint (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdx)) ∧ (retR s).Disjoint (pR (s.gpr .rcx)) ∧
    Reduced s.mem (s.gpr .rsi) ∧ Reduced s.mem (s.gpr .rdx)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (multiplyNTTs (polyAt s.mem (s.gpr .rsi)) (polyAt s.mem (s.gpr .rdx)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

theorem gammaTab_eq {i : Nat} : gammaTab i = (gamma i).val := by
  rw [gamma, val_pow]; rfl

theorem gTab_eq (i : Nat) : gTab i = (gamma i).val * 65536 % 3329 := by rw [gTab, gammaTab_eq]

theorem gTab_lt (i : Nat) : gTab i < 65536 := by
  have : gTab i < 3329 := Nat.mod_lt _ (by decide)
  omega

namespace Mul

section
variable (s₀ : State)
abbrev hP : Addr := s₀.gpr .rdi
abbrev fP : Addr := s₀.gpr .rsi
abbrev gP : Addr := s₀.gpr .rdx
abbrev sP : Addr := s₀.gpr .rcx
abbrev F : Poly := polyAt s₀.mem (fP s₀)
abbrev G : Poly := polyAt s₀.mem (gP s₀)
end

/-- After `i` groups of 16 coefficients. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = coeffAddr (fP s₀) (16 * i)
  rdx : s.gpr .rdx = coeffAddr (gP s₀) (16 * i)
  rdi : s.gpr .rdi = coeffAddr (hP s₀) (16 * i)
  r8 : s.gpr .r8 = wAddr (sP s₀) (8 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : VConsts s
  r2 : s.xmm .xmm12 = r2V
  frame : Frame [pR (hP s₀), pR (sP s₀)] s₀.mem s.mem
  tab : ∀ k < 128, (wordAt s.mem (sP s₀) k).toNat = gTab k
  done : ∀ k < 16 * i, (coeffAt s.mem (hP s₀) k).toNat = ((multiplyNTTs (F s₀) (G s₀))[k]!).val

section
variable {s₀ : State} (hp : mulK.pre s₀)
include hp

theorem inRd {p : Addr} (hp' : p = fP s₀ ∨ p = gP s₀) {j : Nat} (hj : j + 16 ≤ 256) {t : Nat} (ht : t < 4) :
    InRegions (s₀.rd ++ s₀.wr) (coeffAddr p j + BitVec.ofNat 64 (16 * t)) 16 := by
  rw [off16, hp.1, hp.2.1]
  rcases hp' with rfl | rfl
  · exact ⟨pR _, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · exact ⟨pR _, by simp, Offset.contains_base _ (by omega) (by omega)⟩

/-- `f` and `g` are not written. -/
theorem coeffFG {m : Mem} (hf : Frame [pR (hP s₀), pR (sP s₀)] s₀.mem m) {p : Addr} (hp' : p = fP s₀ ∨ p = gP s₀)
    {k : Nat} (hk : k < 256) : (coeffAt m p k).toNat = ((polyAt s₀.mem p)[k]!).val := by
  have hd : ∀ r ∈ [pR (hP s₀), pR (sP s₀)], (polyRegion p).Disjoint r := by
    rcases hp' with rfl | rfl
    · simpa using ⟨hp.2.2.1.symm, hp.2.2.2.2.2.1⟩
    · simpa using ⟨hp.2.2.2.1.symm, hp.2.2.2.2.2.2.1⟩
  have hr : Reduced s₀.mem p := by
    rcases hp' with rfl | rfl
    · exact hp.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hp.2.2.2.2.2.2.2.2.2.2.2.2
  rw [coeffAt_congr (bytes_frame hf hd (by decide)) (by rw [n_eq]; exact hk),
    polyAt_val hr (by rw [n_eq]; exact hk)]

/-- The 16 coefficients from `j` of `f` or `g`, as `deint_lanes` takes them. -/
theorem loads {m : Mem} (hf : Frame [pR (hP s₀), pR (sP s₀)] s₀.mem m) {p : Addr} (hp' : p = fP s₀ ∨ p = gP s₀)
    {j : Nat} (hj : j + 16 ≤ 256) {t : Nat} (ht : t < 4) :
    ∀ e < 4, (dword (m.readW (coeffAddr p j + BitVec.ofNat 64 (16 * t)) 128) e).toNat =
      ((polyAt s₀.mem p)[j + (4 * t + e)]!).val := fun e he => by
  rw [off16, dword_readW _ _ he, coeffAddr_off, ← coeffAt_eq, Nat.add_assoc, coeffFG hp hf hp' (by omega)]

omit hp in
/-- A value of the product, from the lanes `vbase` leaves. -/
theorem prod_val {i : Nat} (hi : i < 16) {X1 X2 : BitVec 128} {F G : Poly}
    (h1 : Lanes X1 fun e => F[16 * i + 2 * e]! * G[16 * i + 2 * e]! +
      F[16 * i + 2 * e + 1]! * G[16 * i + 2 * e + 1]! * gamma (8 * i + e))
    (h2 : Lanes X2 fun e => F[16 * i + 2 * e]! * G[16 * i + 2 * e + 1]! + F[16 * i + 2 * e + 1]! * G[16 * i + 2 * e]!)
    {k : Nat} (hk : k < 16) :
    (word (if k % 2 = 0 then X1 else X2) (k / 2)).toNat = ((multiplyNTTs F G)[16 * i + k]!).val := by
  rw [multiplyNTTs_get F G (by rw [n_eq]; omega)]
  split
  · rename_i he
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), h1 _ (by omega)]
    dsimp only
    rw [show 16 * i + 2 * (k / 2) = 16 * i + k by omega, show (16 * i + k) / 2 = 8 * i + k / 2 by omega]
  · rename_i he
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), h2 _ (by omega)]
    dsimp only
    rw [show 16 * i + 2 * (k / 2) = 16 * i + k - 1 by omega, show 16 * i + k - 1 + 1 = 16 * i + k by omega]

theorem step {i : Nat} (hi : i < 16) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block (mulBody ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hrr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hI.rd, hI.wr]
  have hj : 16 * i + 16 ≤ 256 := by omega
  have rF : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (16 * t)) 16 := fun t ht => by
    rw [hrr, hI.rsi]; exact inRd hp (.inl rfl) hj ht
  have rG : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (16 * t)) 16 := fun t ht => by
    rw [hrr, hI.rdx]; exact inRd hp (.inr rfl) hj ht
  have r0 : ∀ {a : Addr}, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (16 * 0)) 16 →
      InRegions (s.rd ++ s.wr) a 16 := fun h => by rwa [Nat.mul_zero, add_ofNat_zero] at h
  simp only [mulBody, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (deintF_ok (r0 (rF 0 (by decide))) (rF 1 (by decide)) (rF 2 (by decide)) (rF 3 (by decide)))
    fun s1 ⟨e0, e4, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (deintG_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r0 (rG 0 (by decide)))
    (by rw [o1.rd, o1.wr, o1.gpr]; exact rG 1 (by decide)) (by rw [o1.rd, o1.wr, o1.gpr]; exact rG 2 (by decide))
    (by rw [o1.rd, o1.wr, o1.gpr]; exact rG 3 (by decide))) fun s2 ⟨e6, e10, o2⟩ => ?_
  have o12 := o1.trans o2
  have hz : InRegions (s2.rd ++ s2.wr) (s2.gpr .r8) 16 := by
    rw [o12.rd, o12.wr, o12.gpr, hrr, hI.r8, hp.1, hp.2.1]
    exact ⟨pR (sP s₀), by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s3 : State) => s3.xmm .xmm13 = s2.mem.readW (s2.gpr .r8) 128 ∧ XOnly [.xmm13] s2 s3)
    (by vrunm [hz]; xonly) fun s3 ⟨e13, o3⟩ => ?_
  have o123 := o12.trans o3
  -- the lanes `vbase` multiplies
  have LF : ∀ t < 4, ∀ e < 4, (dword (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (16 * t)) 128) e).toNat =
      ((F s₀)[16 * i + (4 * t + e)]!).val := fun t ht => by rw [hI.rsi]; exact loads hp hI.frame (.inl rfl) hj ht
  have LG : ∀ t < 4, ∀ e < 4, (dword (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (16 * t)) 128) e).toNat =
      ((G s₀)[16 * i + (4 * t + e)]!).val := fun t ht => by rw [hI.rdx]; exact loads hp hI.frame (.inr rfl) hj ht
  have DF := deint_lanes (c := fun k => ((F s₀)[16 * i + k]!).val)
    (fun e he => by have := LF 0 (by decide) e he; simpa only [Nat.mul_zero, add_ofNat_zero, Nat.zero_add] using this)
    (fun e he => LF 1 (by decide) e he) (fun e he => LF 2 (by decide) e he) (fun e he => LF 3 (by decide) e he)
    (fun k _ => by have := val_lt ((F s₀)[16 * i + k]!); omega)
  have DG := deint_lanes (c := fun k => ((G s₀)[16 * i + k]!).val)
    (fun e he => by have := LG 0 (by decide) e he; simpa only [Nat.mul_zero, add_ofNat_zero, Nat.zero_add] using this)
    (fun e he => LG 1 (by decide) e he) (fun e he => LG 2 (by decide) e he) (fun e he => LG 3 (by decide) e he)
    (fun k _ => by have := val_lt ((G s₀)[16 * i + k]!); omega)
  have x0 : s3.xmm .xmm0 = s1.xmm .xmm0 := by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]
  have x4 : s3.xmm .xmm4 = s1.xmm .xmm4 := by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]
  have x6 : s3.xmm .xmm6 = s2.xmm .xmm6 := o3.xmm _ (by decide)
  have x10 : s3.xmm .xmm10 = s2.xmm .xmm10 := o3.xmm _ (by decide)
  rw [o1.gpr, o1.mem] at e6 e10
  have hZ : ZLanes (s3.xmm .xmm13) (fun e => gamma (8 * i + e)) := fun e he => by
    rw [e13, o12.mem, o12.gpr, hI.r8, word_readW _ _ he, wAddr_add, ← wordAt, hI.tab _ (by omega), gTab_eq]
  rw [WP.block_append_iff]
  refine WP.mono (vbase_ok (x0 := fun e => (F s₀)[16 * i + 2 * e]!) (x1 := fun e => (F s₀)[16 * i + 2 * e + 1]!)
    (y0 := fun e => (G s₀)[16 * i + 2 * e]!) (y1 := fun e => (G s₀)[16 * i + 2 * e + 1]!)
    (o123.consts hI.c (by decide) (by decide)) (by rw [o123.xmm _ (by decide), hI.r2])
    (fun e he => by rw [x0, e0]; exact DF.1 e he) (fun e he => by rw [x4, e4]; exact DF.2 e he)
    (fun e he => by rw [x6, e6]; exact DG.1 e he) (fun e he => by rw [x10, e10]; exact DG.2 e he) hZ)
    fun s4 ⟨h1, h2, o4⟩ => ?_
  have o1234 := o123.trans o4
  have hw4 : pR (hP s₀) ∈ s4.wr := by rw [o1234.wr, hI.wr, hp.2.1]; simp
  rw [WP.block_append_iff]
  refine WP.mono (vinter_ok hj (by rw [o1234.gpr, hI.rdi]) hw4)
    fun s5 ⟨out, inr, f5, g5, rd5, wr5, mx5, x5⟩ => ?_
  have sx64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (4 * 16) := by decide
  vrunm [g5, o1234.gpr, sx64]
  have tS : ∀ k < 128, wordAt s5.mem (sP s₀) k = wordAt s.mem (sP s₀) k := fun k hk => by
    rw [wordAt, f5.readW (r := pR (sP s₀)) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.2.2.2.2.1.symm) (by decide), o1234.mem]; rfl
  constructor
  all_goals try simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.xmm_setReg, RegUpd.xmm_setFlags, setReg_mem, setFlags_mem,
    reduceCtorEq, ite_true, ite_false]
  case rsi => rw [hI.rsi, coeffAddr_off, Nat.mul_succ]
  case rdx => rw [hI.rdx, coeffAddr_off, Nat.mul_succ]
  case rdi => rw [hI.rdi, coeffAddr_off, Nat.mul_succ]
  case r8 => rw [hI.r8, show (16 : BitVec 64) = BitVec.ofNat 64 (2 * 8) from rfl, wAddr_add, Nat.mul_succ]
  case rd => rw [rd5, o1234.rd, hI.rd]
  case wr => rw [wr5, o1234.wr, hI.wr]
  case c =>
    refine ⟨?_, ?_⟩ <;> simp only [RegUpd.xmm_setReg, RegUpd.xmm_setFlags]
    · rw [x5 _ (by decide), o1234.xmm _ (by decide), hI.c.q]
    · rw [x5 _ (by decide), o1234.xmm _ (by decide), hI.c.qinv]
  case r2 => rw [x5 _ (by decide), o1234.xmm _ (by decide), hI.r2]
  case frame => exact hI.frame.trans (by rw [← o1234.mem]; exact f5.mono (by simp))
  case tab => exact fun k hk => by rw [tS k hk]; exact hI.tab k hk
  case done =>
    intro k hk
    by_cases hk' : k < 16 * i
    · rw [out k (by omega) (.inl hk'), o1234.mem]; exact hI.done k hk'
    · obtain ⟨k', rfl⟩ : ∃ k', k = 16 * i + k' := ⟨k - 16 * i, by omega⟩
      rw [inr k' (by omega)]
      exact prod_val hi h1 h2 (by omega)

theorem correct : ∃ t s', Exec isa Impl.MlKem.X86_64.multiplyNTTs s₀ t s' ∧ abiPreserved s₀ s' ∧
    mulK.post s₀ s' := by
  have hw : pR (sP s₀) ∈ s₀.wr := by rw [hp.2.1]; simp
  have hW : WP isa Impl.MlKem.X86_64.multiplyNTTs s₀ fun s' => ∃ s3,
      (PolyIs s3.mem (hP s₀) (multiplyNTTs (F s₀) (G s₀)) ∧ Frame [pR (hP s₀), pR (sP s₀)] s₀.mem s3.mem) ∧
      Frame [mxR (sP s₀)] s3.mem s'.mem ∧ Keep [] s3 s' := by
    unfold Impl.MlKem.X86_64.multiplyNTTs
    refine WP.seq (WP.mono (Q := fun (s1 : State) => s1.gpr .r10 = sP s₀ ∧ s1.mem = s₀.mem ∧
      s1.xmm = s₀.xmm ∧ Keep [.r10] s₀ s1) (by
        vrunm
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s1 ⟨h10, hm1, _, k1⟩ => ?_)
    refine withMxcsr_ok (by decide) [.rax, .rcx, .rdx, .rdi, .rsi, .r8, .r9] (by decide) h10
      (by rw [k1.2.2]; exact hw) ?_ fun s2 k2 f2 => ?_
    · decide +kernel
    have k12 := k1.trans k2
    have h10' : s2.gpr .r10 = sP s₀ := by rw [k2.gpr (by decide), h10]
    refine WP.seq ?_
    simp only [mulPro, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (wordTab_gen gTab gTab_lt (by decide) h10' (by rw [k12.2.2]; exact hw))
      fun s3 ⟨ht, f3, k3, _, _⟩ => ?_
    have h10'' : s3.gpr .r10 = sP s₀ := by rw [k3.gpr (by decide), h10']
    refine WP.mono (Q := fun (s4 : State) => VConsts s4 ∧ s4.xmm .xmm12 = r2V ∧ s4.gpr .r8 = sP s₀ ∧
      s4.mem = s3.mem ∧ Keep [.rax, .r8] s3 s4) (by
        simp only [vconsts]
        vrunm [h10'']
        refine ⟨⟨?_, ?_⟩, fun r hr => ?_, rfl, rfl⟩
        · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true, ite_false, reduceCtorEq]
          decide
        · simp only [RegUpd.xmm_setReg, xmm_setXmm, ite_true, ite_false, reduceCtorEq]
          decide
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false])
      fun s4 ⟨hc4, hr4, h84, hm4, k4⟩ => ?_
    have k14 := (k12.trans k3).trans k4
    refine WP.mono (wp_rcxLoop (N := 16) (by decide) (by decide) (Inv s₀) (fun s g _ => ?_)
      fun i hi s hI => step hp hi hI) fun s5 hI => ⟨?_, hI.frame⟩
    · have k := k14.trans g.keep
      refine ⟨?_, ?_, ?_, ?_, by rw [k.2.1], by rw [k.2.2], ?_, ?_, ?_, ?_, fun _ h => absurd h (by omega)⟩
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [g.keep.gpr (by decide), h84]; exact (add_ofNat_zero _).symm
      · exact ⟨by rw [g.xmm]; exact hc4.q, by rw [g.xmm]; exact hc4.qinv⟩
      · rw [g.xmm]; exact hr4
      · rw [g.mem, hm4, ← hm1]
        refine (frame_fs (fP := hP s₀) f2 ?_).trans (frame_fs f3 ?_) <;>
          intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
        exacts [.inr (mx_sub _), .inr (pR_sub_tab _)]
      · intro k hk; rw [g.mem, hm4]; exact ht k hk
    · exact polyIs_of_toNat fun k hk => hI.done k (by rw [n_eq] at hk; omega)
  obtain ⟨t, s', he, ⟨s3, ⟨hP', hf⟩, hf', -⟩, hk⟩ :=
    WP.keep [.rax, .rcx, .rdx, .rdi, .rsi, .r8, .r9, .r10, .r11] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_ctl (by decide +kernel) he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.2.2.2.2.1.sub_right (mx_sub _)) hP'

end

end Mul

theorem mul_correct (s : State) (hs : mulK.pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.multiplyNTTs s t s' ∧ abiPreserved s s' ∧ mulK.post s s' :=
  Mul.correct hs

theorem mul_ct : ConstantTime isa mulK.pre mulK.pub Impl.MlKem.X86_64.multiplyNTTs :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def mulSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x4000, 1024⟩]

theorem mul_verified :
    Verified X86_64.target Impl.MlKem.X86_64.multiplyNTTs (Spec.MlKem.mulContract X86_64.abi) :=
  Verified.of_correct mul_correct mul_ct (by
    mlkem_implies [Spec.MlKem.mulContract, Spec.MlKem.mulSig, mulK, X86_64.abi, X86_64.argRegs]
      [mulSat] using mulSat)

end VG.Proof.MlKem.X86_64
