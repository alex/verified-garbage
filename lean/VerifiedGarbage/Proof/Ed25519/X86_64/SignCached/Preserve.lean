import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Hashes
import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Reduce
import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Base
import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.MulAdd
import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Prefix
import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Wipe

/-! Byte-level consequences of each call's exact memory frame. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Proof.Ed25519.X86_64.PublicKey (within_base)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (r : Region)
    (hd : ∀ R ∈ rs, r.Disjoint R) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  apply List.map_congr_left
  intro i hi
  exact Frame.bytes hf hd hn (List.mem_range.mp hi)

theorem Ctx.input_bytes (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {r : Region}
    (hr : r ∈ L.inputs) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.mem r.base r.len = Spec.Ed25519.bytesAt m₀ r.base r.len := by
  apply List.map_congr_left
  intro i hi
  exact hc.input_byte hL hr hn (List.mem_range.mp hi)

theorem single_stk_bytes {m m' : Mem} {d n e k : Nat}
    (hf : Frame [⟨L.B + BitVec.ofNat 64 e, k⟩] m m')
    (hsep : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 264) (he : e + k ≤ 264) :
    Spec.Ed25519.bytesAt m' (L.B + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.B + BitVec.ofNat 64 d) n := by
  exact frame_bytes hf ⟨L.B + BitVec.ofNat 64 d, n⟩ (by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ hsep (by omega) (by omega)) (by change n ≤ 2 ^ 64; omega)

theorem hash_stk_bytes (hL : L.Ok) {m m' : Mem} (hf : HashFrame L m m') {d n : Nat}
    (hd : 16 ≤ d) (hn : d + n ≤ 144) :
    Spec.Ed25519.bytesAt m' (L.B + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.B + BitVec.ofNat 64 d) n := by
  refine frame_bytes hf ⟨L.B + BitVec.ofNat 64 d, n⟩ ?_ (by change n ≤ 2 ^ 64; omega)
  intro r hr
  simp only [hashWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using hL.stk_scr (d := d) (n := n) (e := 0) (k := 8192) (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · exact Offset.disjoint_base _ hd (by omega)

theorem reduce_stk_bytes (hL : L.Ok) {m m' : Mem} {out d n : Nat}
    (hf : Frame (reduceWr L out ++ [⟨L.B, 16⟩]) m m')
    (hd : 16 ≤ d) (hn : d + n ≤ 264) (ho : out + 32 ≤ 128)
    (hsep : d + n ≤ 16 + out ∨ 16 + out + 32 ≤ d) :
    Spec.Ed25519.bytesAt m' (L.B + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.B + BitVec.ofNat 64 d) n := by
  refine frame_bytes hf ⟨L.B + BitVec.ofNat 64 d, n⟩ ?_ (by change n ≤ 2 ^ 64; omega)
  intro r hr
  simp only [reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ hsep (by omega) (by omega)
  · simpa using hL.stk_scr (d := d) (n := n) (e := 0) (k := 8192) (by omega) (by omega)
  · exact Offset.disjoint_base _ hd (by omega)

theorem base_stk_bytes (hL : L.Ok) {m m' : Mem} (hf : Frame (baseWr L ++ [⟨L.B, 16⟩]) m m')
    {d n : Nat} (hd : 16 ≤ d) (hn : d + n ≤ 264) :
    Spec.Ed25519.bytesAt m' (L.B + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.B + BitVec.ofNat 64 d) n := by
  refine frame_bytes hf ⟨L.B + BitVec.ofNat 64 d, n⟩ ?_ (by change n ≤ 2 ^ 64; omega)
  intro r hr
  simp only [baseWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hL.ko.sub_left (Offset.sub_base _ hn)).sub_right (within_base _ (by decide : 32 ≤ 64)).sub
  · simpa using hL.stk_scr (d := d) (n := n) (e := 0) (k := 8192) (by omega) (by omega)
  · exact Offset.disjoint_base _ hd (by omega)

theorem reduce_out_bytes (hL : L.Ok) {m m' : Mem} {out : Nat}
    (hf : Frame (reduceWr L out ++ [⟨L.B, 16⟩]) m m') (ho : out + 32 ≤ 128) :
    Spec.Ed25519.bytesAt m' L.out 32 = Spec.Ed25519.bytesAt m L.out 32 := by
  have hs := (within_base L.out (by decide : 32 ≤ 64)).sub
  refine frame_bytes hf ⟨L.out, 32⟩ ?_ (by decide : 32 ≤ 2 ^ 64)
  intro r hr
  simp only [reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ((hL.ko.sub_left (Offset.sub_base _ (by omega))).sub_right hs).symm
  · exact hL.oc.sub_left hs
  · exact ((hL.ko.sub_left (within_base _ (by decide : 16 ≤ 264)).sub).sub_right hs).symm

theorem mul_out_bytes (hL : L.Ok) {m m' : Mem} (hf : Frame (mulWr L ++ [⟨L.B, 16⟩]) m m') :
    Spec.Ed25519.bytesAt m' L.out 32 = Spec.Ed25519.bytesAt m L.out 32 := by
  refine frame_bytes hf ⟨L.out, 32⟩ ?_ (by decide : 32 ≤ 2 ^ 64)
  intro r hr
  simp only [mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.base_disjoint _ (by decide) (by decide)
  · exact hL.oc.sub_left (within_base _ (by decide : 32 ≤ 64)).sub
  · exact ((hL.ko.sub_left (within_base _ (by decide : 16 ≤ 264)).sub).sub_right
      (within_base _ (by decide : 32 ≤ 64)).sub).symm

end VG.Proof.Ed25519.X86_64.SignCached
