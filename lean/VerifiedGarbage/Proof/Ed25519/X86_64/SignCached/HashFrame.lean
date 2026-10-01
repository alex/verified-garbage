import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Hash

/-! Memory preserved across a complete signing hash. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (Within within_base within_off)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

abbrev hashWr (L : Lay) : List Region := [L.SCR, ⟨L.B + BitVec.ofNat 64 144, 64⟩, ⟨L.B, 16⟩]
abbrev HashFrame (L : Lay) (m m' : Mem) := Frame (hashWr L) m m'

theorem init_frame {m m' : Mem} (hf : Frame (initWr L ++ [⟨L.B, 16⟩]) m m') :
    HashFrame L m m' := by
  refine hf.sub fun r hr => ?_
  simp only [initWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨L.SCR, by simp, (within_base _ (by decide : 192 ≤ 8192)).sub⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem upd_frame {m m' : Mem} (hf : Frame (updWr L ++ [⟨L.B, 16⟩]) m m') :
    HashFrame L m m' := by
  refine hf.sub fun r hr => ?_
  simp only [updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨L.SCR, by simp, (within_base _ (by decide : 192 ≤ 8192)).sub⟩
  · exact ⟨L.SCR, by simp, Offset.sub_base L.scr (d := 192) (n := 1376) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem fin_frame {m m' : Mem} (hf : Frame (finWr L ++ [⟨L.B, 16⟩]) m m') :
    HashFrame L m m' := by
  refine hf.sub fun r hr => ?_
  simp only [finWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨L.SCR, by simp, (within_base _ (by decide : 192 ≤ 8192)).sub⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨L.SCR, by simp, Offset.sub_base L.scr (d := 192) (n := 1376) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

structure Stable (L : Lay) (r : Region) : Prop extends Input L r where
  digest : r.Disjoint ⟨L.B + BitVec.ofNat 64 144, 64⟩

theorem Stable.bytes {r : Region} (hi : Stable L r) {m m' : Mem} (hf : HashFrame L m m')
    (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i h => Frame.bytes hf ?_ hn (List.mem_range.mp h)
  intro R hR
  simp only [hashWr, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact hi.scratch
  · exact hi.digest
  · exact hi.below.symm

theorem stable_input (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs) : Stable L r := by
  refine ⟨⟨⟨r, List.mem_append_left _ hr, within_base _ (by omega)⟩, hL.sc r hr,
    by simpa using hL.stk_input hr (d := 0) (n := 16) (by omega)⟩,
    (hL.stk_input hr (d := 144) (n := 64) (by omega)).symm⟩

theorem stable_out (hL : L.Ok) : Stable L ⟨L.out, 32⟩ := by
  have hs : Within (⟨L.out, 32⟩ : Region) L.OUT := within_base _ (by decide)
  exact ⟨⟨⟨L.OUT, by simp, hs⟩, hL.oc.sub_left hs.sub,
    (hL.ko.sub_left ((within_base _ (by decide : 16 ≤ 264)).sub)).sub_right hs.sub⟩,
    ((hL.ko.sub_left (Offset.sub_base L.B (d := 144) (n := 64) (by decide))).sub_right hs.sub).symm⟩

theorem stable_prefix (hL : L.Ok) : Stable L ⟨L.B + BitVec.ofNat 64 48, 32⟩ := by
  refine ⟨⟨⟨L.FR, by simp, 32, by rw [PublicKey.add_add], by show 32 + 32 ≤ 248; decide⟩,
    ?_, ?_⟩, ?_⟩
  · simpa using hL.stk_scr (d := 48) (n := 32) (e := 0) (k := 8192) (by omega) (by omega)
  · exact Offset.base_disjoint _ (by decide) (by decide)
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)

end VG.Proof.Ed25519.X86_64.SignCached
