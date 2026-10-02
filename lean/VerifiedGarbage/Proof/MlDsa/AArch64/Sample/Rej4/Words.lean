import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (seedWord)

def seedR (p : Addr) : Region := ⟨p,34⟩
def seedAddr (p : Addr) (j : Nat) : Addr := p+BitVec.ofNat 64 (8*j)

def PartAt (m : Mem) (p : Addr) (src : Mem) (a b : Addr) (n : Nat) : Prop :=
  ∀ i < 25, m.read (wordAddr p i) 16 =
    if i < n then ofVDwords (src.readW (seedAddr a i) 64) (src.readW (seedAddr b i) 64) else 0

theorem seed_contains (p : Addr) {j : Nat} (hj : j < 4) :
    (seedR p).Contains (seedAddr p j) 8 := Offset.contains_base p (by omega) (by omega)

/-- Absorb the first 32 bytes of both seeds into corresponding packed lanes. -/
theorem seedWords_ok {s : State} {p a b : Addr}
    (hp : s.gpr .x2 = p) (ha : s.gpr .x3 = a) (hb : s.gpr .x4 = b)
    (hina : ∀ j < 4, InRegions (s.rd++s.wr) (seedAddr a j) 8)
    (hinb : ∀ j < 4, InRegions (s.rd++s.wr) (seedAddr b j) 8)
    (hw : ∀ j < 4, InRegions s.wr (wordAddr p j) 16)
    (hda : (seedR a).Disjoint (pairR p)) (hdb : (seedR b).Disjoint (pairR p))
    (hz : ∀ i < 25, s.mem.read (wordAddr p i) 16 = 0) :
    WP isa (.block ((List.range 4).flatMap seedWord)) s fun t =>
      RegKeep [.x6,.x7] s t ∧ Frame [pairR p] s.mem t.mem ∧ PartAt t.mem p s.mem a b 4 := by
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x6,.x7] s t ∧ Frame [pairR p] s.mem t.mem ∧ PartAt t.mem p s.mem a b k)
    (fun k t hk ⟨ht,hf,hvals⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,Frame.refl _ _,fun i hi => by rw [ite_eq_right (Nat.not_lt_zero _)]; exact hz i hi⟩
  refine WP.mono (seedWord_ok hk
    ((ht.gpr .x2 (by decide)).trans hp) ((ht.gpr .x3 (by decide)).trans ha)
    ((ht.gpr .x4 (by decide)).trans hb)
    (by rw [ht.rd,ht.wr]; exact hina k hk) (by rw [ht.rd,ht.wr]; exact hinb k hk)
    (by rw [ht.wr]; exact hw k hk)) fun u ⟨hu,hm⟩ => ?_
  have hra : t.mem.readW (seedAddr a k) 64 = s.mem.readW (seedAddr a k) 64 :=
    hf.readW (seed_contains a hk) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hda) (by decide)
  have hrb : t.mem.readW (seedAddr b k) 64 = s.mem.readW (seedAddr b k) 64 :=
    hf.readW (seed_contains b hk) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hdb) (by decide)
  change u.mem = t.mem.write (wordAddr p k) 16 (ofVDwords
    (t.mem.readW (seedAddr a k) 64) (t.mem.readW (seedAddr b k) 64)) at hm
  rw [hra,hrb] at hm
  refine ⟨(ht.trans hu).mono (by simp),?_,?_⟩
  · rw [hm]; exact hf.write (List.mem_singleton_self _) _ (pair_contains p (by omega))
  · intro i hi
    rw [hm]
    by_cases he : i = k
    · subst i
      rw [read_write16,ite_eq_left (by omega)]
    · have hs : Mem.Sep (wordAddr p i) 16 (wordAddr p k) 16 :=
        Offset.sep p (d := 16*i) (e := 16*k) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hs (by decide),hvals i hi]
      by_cases hl : i < k
      · rw [ite_eq_left hl,ite_eq_left (by omega)]
      · rw [ite_eq_right hl,ite_eq_right (by omega)]
end VG.Proof.MlDsa.AArch64.Sample.Rej4
