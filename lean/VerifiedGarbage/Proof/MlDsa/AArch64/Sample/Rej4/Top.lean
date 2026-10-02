import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Parse
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Epi

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_movz wp_nil)
open VG.Proof.MlDsa.Sample (Stored stored_frame stored_polyIs rnFold_length_le)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (sample epi rejNTT4With)

def mask (σ : State) (n : Nat) : BitVec 64 :=
  if (List.range n).all (fun k => (L σ k).length == 256) then 1 else 0

theorem mask_step (σ : State) (n : Nat) : mask σ n &&& result σ n = mask σ (n+1) := by
  have er : result σ n = if (L σ n).length == 256 then (1 : BitVec 64) else 0 := by
    simp only [result,beq_iff_eq]
  rw [er]
  simp only [mask,List.range_succ,List.all_append,List.all_cons,List.all_nil,Bool.and_true]
  cases (List.range n).all (fun k => (L σ k).length == 256) <;>
    cases (L σ n).length == 256 <;> rfl

structure Parsed (σ : State) (n : Nat) (s : State) : Prop where
  ready : Ready σ s
  mask : s.gpr .x27 = mask σ n
  stored : ∀ k < n,Stored s.mem (polyP σ k) (L σ k)

theorem parsed_step {σ s : State} (hp : Pre σ) {n : Nat} (hn : n < 4) (h : Parsed σ n s) :
    WP isa (sample n) s (Parsed σ (n+1)) := by
  refine WP.mono (sample_ok hp h.ready hn) fun t ⟨hr,_,hf,hs,hm⟩ => ⟨hr,?_,fun k hk => ?_⟩
  · rw [hm,h.mask,mask_step]
  · by_cases he : k = n
    · subst k; exact hs
    · exact stored_frame hf (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint (aP σ) (d := 1024*k) (e := 1024*n) (n := 1024) (k := 1024)
          (by omega) (by omega) (by omega)) (h.stored k (by omega)) (rnFold_length_le (by simp) _)

def r4K : Contract isa where
  pre := Pre
  post s t := (t.gpr .x0).setWidth 32 = (mask s 4).setWidth 32 ∧
    ∀ k < 4,(L s k).length = 256 → Spec.MlDsa.PolyIs t.mem (polyP s k) (VG.Proof.MlDsa.Sample.toPoly (L s k))
  pub s t := seedP s = seedP t ∧ aP s = aP t ∧ scr s = scr t ∧ s.sp = t.sp ∧
    Spec.Sha3.bytesAt s.mem (seedP s) 136 = Spec.Sha3.bytesAt t.mem (seedP t) 136

theorem end_ok {σ s : State} (hp : Pre σ) (h : Parsed σ 4 s) :
    WP isa (.block epi) s fun t => abiPreserved σ t ∧ r4K.post σ t := by
  refine WP.mono (epi_ok hp h.ready.env) fun t ⟨hab,hm,h0,_,_⟩ => ⟨hab,?_,fun k hk he => ?_⟩
  · rw [h0,h.mask]
  · rw [hm]; exact stored_polyIs (h.stored k hk) he

theorem body_ok {σ s : State} (hp : Pre σ) (h : Ready σ s) :
    WP isa (.seq (.block [.movz .x .x27 1 0])
      (.seq (sample 0) (.seq (sample 1) (.seq (sample 2) (.seq (sample 3) (.block epi)))))) s
      fun t => abiPreserved σ t ∧ r4K.post σ t := by
  refine WP.seq (wp_movz fun t ht et => wp_nil ?_)
  have hr := h.polyStep hp (k := 0) (by decide) (by rw [ht.mem]; exact Frame.refl _ _)
    ht.rd ht.wr ht.sp (fun r hr => ht.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  have h0 : Parsed σ 0 t := ⟨hr,by rw [et]; rfl,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  exact WP.seq (WP.mono (parsed_step hp (by decide) h0) fun _ h1 =>
    WP.seq (WP.mono (parsed_step hp (by decide) h1) fun _ h2 =>
      WP.seq (WP.mono (parsed_step hp (by decide) h2) fun _ h3 =>
        WP.seq (WP.mono (parsed_step hp (by decide) h3) fun _ h4 => end_ok hp h4))))

theorem correct (sha3 : Bool) (σ : State) (hp : r4K.pre σ) :
    ∃ tr t,Exec isa (rejNTT4With sha3) σ tr t ∧ abiPreserved σ t ∧ r4K.post σ t := by
  unfold rejNTT4With
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (init_ok hp) fun s ⟨he,h0,h1⟩ => ?_
  refine WP.mono (setup_ok he h0 h1) fun u hu => ?_
  refine WP.seq (WP.mono (squeeze_ok sha3 hp hu) fun t ht => body_ok hp ⟨ht.env,fun k hk j hj =>
    ht.out k hk j (by simpa using hj)⟩)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
