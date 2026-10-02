import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Squeeze
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

structure BlockKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x16 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem roundsProg_ok (sha3 : Bool) {n : Nat} (hn : n ≤ 24) {s : State} {A B : Spec.Sha3.State}
    (hp : Pairs s A B) : WP isa (Impl.Sha3.AArch64.Neon.Pair.roundsProg sha3 n) s fun t =>
      CoreKeep s t ∧ Pairs t ((List.range n).foldl Spec.Sha3.rnd A) ((List.range n).foldl Spec.Sha3.rnd B) := by
  induction n generalizing s A B with
  | zero => exact WP.block_nil_iff.mpr ⟨CoreKeep.refl _,hp⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega) hp) fun u ⟨hu,hpu⟩ => ?_)
    have hr : WP isa (.block (if sha3 then Impl.Sha3.AArch64.Sha3.Vector.round n else
        Impl.Sha3.AArch64.Neon.Vector.round n)) u fun t => CoreKeep u t ∧
          Pairs t (Spec.Sha3.rnd ((List.range n).foldl Spec.Sha3.rnd A) n)
            (Spec.Sha3.rnd ((List.range n).foldl Spec.Sha3.rnd B) n) := by
      cases sha3
      · exact round_ok hpu (by omega)
      · exact Hw.round2_ok hpu (by omega)
    refine WP.mono hr fun t ⟨ht,hpt⟩ => ⟨hu.trans ht,?_⟩
    simpa only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil] using hpt

/-- One permutation and one output block for two independent SHAKE128 streams. -/
theorem prog_okWith (sha3 : Bool) {s : State} {p a b : Addr} {rp ra rb : Reg} {A B : Spec.Sha3.State}
    (hp : s.gpr rp = p) (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (ha16 : ra ≠ .x16)
    (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7) (hb16 : rb ≠ .x16) (hp16 : rp ≠ .x16)
    (hpair : PairAt s.mem p A B)
    (hin : ∀ i < 25, InRegions (s.rd++s.wr) (wordAddr p i) 16)
    (hwp : ∀ i < 25, InRegions s.wr (wordAddr p i) 16)
    (hwa : ∀ i < 21, InRegions s.wr (outAddr a i) 8)
    (hwb : ∀ i < 21, InRegions s.wr (outAddr b i) 8)
    (hd : (outR a).Disjoint (outR b))
    (hpa : (pairR p).Disjoint (outR a)) (hpb : (pairR p).Disjoint (outR b)) :
    WP isa (Impl.Sha3.AArch64.Neon.Pair.progWith sha3 rp ra rb) s fun t =>
      BlockKeep s t ∧ PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      RateAt t.mem a (Spec.Sha3.keccakF A) ∧ RateAt t.mem b (Spec.Sha3.keccakF B) ∧
      Frame [pairR p,outR a,outR b] s.mem t.mem := by
  unfold Impl.Sha3.AArch64.Neon.Pair.progWith
  refine WP.seq (WP.mono (load_ok hp hpair hin) fun s1 ⟨h1,hpair1⟩ => ?_)
  refine WP.seq (WP.mono (roundsProg_ok sha3 (by decide : 24 ≤ 24) hpair1) fun s2 ⟨h2,hpair2⟩ => ?_)
  refine WP.seq (WP.mono (store_ok ((h2.gpr rp hp16).trans ((congrFun h1.gpr rp).trans hp)) hpair2
    (fun i hi => by rw [h2.wr,h1.wr]; exact hwp i hi)) fun s3 ⟨h3,hpair3,hf3⟩ => ?_)
  refine WP.mono (squeeze_ok (A := Spec.Sha3.keccakF A) (B := Spec.Sha3.keccakF B)
    (by rw [h3.gpr,h2.gpr ra ha16,h1.gpr,ha])
    (by rw [h3.gpr,h2.gpr rb hb16,h1.gpr,hb]) ha6 ha7 hb6 hb7
    (by intro i hi; rw [h3.v]; exact hpair2 i hi) hd
    (fun i hi => by rw [h3.wr,h2.wr,h1.wr]; exact hwa i hi)
    (fun i hi => by rw [h3.wr,h2.wr,h1.wr]; exact hwb i hi)) fun t ⟨h4,hra,hrb,hf4⟩ => ?_
  refine ⟨⟨fun r h6 h7 h16 => by rw [h4.gpr r h6 h7,h3.gpr,h2.gpr r h16,h1.gpr],
    h4.rd.trans (h3.rd.trans (h2.rd.trans h1.rd)),
    h4.wr.trans (h3.wr.trans (h2.wr.trans h1.wr)),
    h4.sp.trans (h3.sp.trans (h2.sp.trans h1.sp))⟩,?_,hra,hrb,?_⟩
  · intro i hi
    rw [hf4.read (pair_contains p hi) (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl; exact hpa; exact hpb) (by decide)]
    exact hpair3 i hi
  · have hf3' : Frame [pairR p,outR a,outR b] s.mem s3.mem := by
      rw [← h1.mem,← h2.mem]
      exact hf3.sub (fun r hr => ⟨r,by simp only [List.mem_singleton] at hr; subst r; exact List.mem_cons_self,fun _ h => h⟩)
    exact hf3'.trans (hf4.sub (fun r hr => ⟨r,List.mem_cons_of_mem _ hr,fun _ h => h⟩))
end VG.Proof.Sha3.AArch64.Neon
