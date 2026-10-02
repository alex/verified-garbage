import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Words

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

/-- Padding changes only the two padding words of each packed state. -/
theorem part_pad {m src : Mem} {p a b : Addr} (h : PartAt m p src a b 4) :
    PairAt ((m.write (wordAddr p 4) 16 (ofVDwords (tailWord src a) (tailWord src b))).write
      (wordAddr p 20) 16 (ofVDwords 0x8000000000000000 0x8000000000000000)) p
      (seedState src a) (seedState src b) := by
  intro i hi
  rw [seedState_get src a hi,seedState_get src b hi]
  by_cases h20 : i = 20
  · subst i
    rw [read_write16]
    simp (disch := omega) only [ite_true,ite_eq_right]
  · have hs20 : Mem.Sep (wordAddr p i) 16 (wordAddr p 20) 16 :=
      Offset.sep p (d := 16*i) (e := 16*20) (n := 16) (k := 16) (by omega) (by omega) (by omega)
    rw [Mem.read_write_sep hs20 (by decide)]
    by_cases h4 : i = 4
    · subst i
      rw [read_write16]
      simp (disch := omega) only [ite_true,ite_eq_right]
    · have hs4 : Mem.Sep (wordAddr p i) 16 (wordAddr p 4) 16 :=
        Offset.sep p (d := 16*i) (e := 16*4) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hs4 (by decide),h i hi]
      by_cases hl : i < 4
      · simp only [ite_eq_left hl]
        rfl
      · simp only [ite_eq_right hl,ite_eq_right h4,ite_eq_right h20]
        rfl

theorem seed_byte_frame {m m' : Mem} {p a : Addr} (hf : Frame [pairR p] m m')
    (hd : (seedR a).Disjoint (pairR p)) {j : Nat} (hj : j < 34) :
    m' (a+BitVec.ofNat 64 j) = m (a+BitVec.ofNat 64 j) :=
  hf _ (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd _ (Offset.contains_base a (by omega) (by omega)))

theorem tailWord_frame {m m' : Mem} {p a : Addr} (hf : Frame [pairR p] m m')
    (hd : (seedR a).Disjoint (pairR p)) : tailWord m' a = tailWord m a := by
  unfold tailWord lastWord
  rw [show a+32 = a+BitVec.ofNat 64 32 from rfl,show a+33 = a+BitVec.ofNat 64 33 from rfl,
    seed_byte_frame hf hd (by decide : 32 < 34),seed_byte_frame hf hd (by decide : 33 < 34)]
end VG.Proof.MlDsa.AArch64.Sample.Rej4
