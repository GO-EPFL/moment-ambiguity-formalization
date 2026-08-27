import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite ordered hypergraph Ramsey theorem

This module proves the finite Ramsey theorem for colourings of increasing tuples.  The
formulation by order embeddings avoids quotienting tuples by permutations and is convenient
for the secretary homogenisation argument.
-/

namespace MomentAmbiguity

noncomputable section

/-- A colouring is homogeneous on `H` when all increasing `k`-subtuples of `H` have one colour. -/
def OrderedTupleHomogeneous {k n l : ℕ} {κ : Type*}
    (c : (Fin k ↪o Fin n) → κ) (H : Fin l ↪o Fin n) : Prop :=
  ∃ colour : κ, ∀ e : Fin k ↪o Fin l, c (e.trans H) = colour

/-- Prepend the least point to an increasing tuple. -/
def prependZeroOrderEmb {k n : ℕ} (e : Fin k ↪o Fin n) :
    Fin (k + 1) ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono
    (Fin.cases 0 (fun i ↦ Fin.succ (e i))) (by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => simp at hij
          | succ j => simp
      | succ i =>
          cases j using Fin.cases with
          | zero => simp at hij
          | succ j =>
              simp only [Fin.cases_succ, Fin.succ_lt_succ_iff]
              exact e.strictMono (Fin.succ_lt_succ_iff.mp hij))

@[simp]
theorem prependZeroOrderEmb_zero {k n : ℕ} (e : Fin k ↪o Fin n) :
    prependZeroOrderEmb e 0 = 0 := rfl

@[simp]
theorem prependZeroOrderEmb_succ {k n : ℕ} (e : Fin k ↪o Fin n) (i : Fin k) :
    prependZeroOrderEmb e i.succ = (e i).succ := rfl

/-- Remove the initial zero from an increasing tuple whose first entry is zero. -/
def tailOrderEmbOfZero {k n : ℕ} (e : Fin (k + 1) ↪o Fin (n + 1))
    (hzero : e 0 = 0) : Fin k ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ Fin.pred (e i.succ) (by
      have hlt : e 0 < e i.succ := e.strictMono (by simp)
      rw [hzero] at hlt
      exact ne_of_gt hlt)) (by
        intro i j hij
        rw [Fin.pred_lt_pred_iff]
        exact e.strictMono (by simpa using hij))

@[simp]
theorem succ_tailOrderEmbOfZero {k n : ℕ} (e : Fin (k + 1) ↪o Fin (n + 1))
    (hzero : e 0 = 0) (i : Fin k) :
    (tailOrderEmbOfZero e hzero i).succ = e i.succ := by
  simp [tailOrderEmbOfZero]

/-- Subtract one from every entry of a positive increasing tuple. -/
def predOrderEmbOfPositive {k n : ℕ} (e : Fin (k + 1) ↪o Fin (n + 1))
    (hpos : e 0 ≠ 0) : Fin (k + 1) ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ Fin.pred (e i) (by
      intro hi
      apply hpos
      apply le_antisymm
      · simpa [hi] using e.monotone (Fin.zero_le i)
      · exact Fin.zero_le _)) (by
        intro i j hij
        rw [Fin.pred_lt_pred_iff]
        exact e.strictMono hij)

@[simp]
theorem succ_predOrderEmbOfPositive {k n : ℕ} (e : Fin (k + 1) ↪o Fin (n + 1))
    (hpos : e 0 ≠ 0) (i : Fin (k + 1)) :
    (predOrderEmbOfPositive e hpos i).succ = e i := by
  simp [predOrderEmbOfPositive]

/-- A reservoir whose tuple colour depends only on the least chosen reservoir index. -/
def LeastIndexCanonical {k T n : ℕ} {κ : Type*}
    (c : (Fin (k + 1) ↪o Fin n) → κ) (X : Fin T ↪o Fin n)
    (d : Fin T → κ) : Prop :=
  ∀ e : Fin (k + 1) ↪o Fin T, c (e.trans X) = d (e 0)

/-- The finite reservoir construction used in the successor-uniformity Ramsey step. -/
theorem exists_leastIndexCanonical
    (k : ℕ) {κ : Type*} [Fintype κ] [Nonempty κ]
    (hRamsey : ∀ l : ℕ, ∃ n : ℕ, l ≤ n ∧
      ∀ c : (Fin k ↪o Fin n) → κ,
        ∃ H : Fin l ↪o Fin n, OrderedTupleHomogeneous c H) :
    ∀ T : ℕ, ∃ n : ℕ, T ≤ n ∧
      ∀ c : (Fin (k + 1) ↪o Fin n) → κ,
        ∃ X : Fin T ↪o Fin n, ∃ d : Fin T → κ,
          LeastIndexCanonical c X d := by
  intro T
  induction T with
  | zero =>
      refine ⟨0, le_rfl, fun c ↦ ?_⟩
      refine ⟨(OrderIso.refl (Fin 0)).toOrderEmbedding, Fin.elim0, ?_⟩
      intro e
      exact Fin.elim0 (e 0)
  | succ T ih =>
      obtain ⟨nTail, hTnTail, hTail⟩ := ih
      obtain ⟨nRem, hnTailRem, hRem⟩ := hRamsey nTail
      refine ⟨nRem + 1, Nat.succ_le_succ (hTnTail.trans hnTailRem), fun c ↦ ?_⟩
      let c0 : (Fin k ↪o Fin nRem) → κ := fun e ↦ c (prependZeroOrderEmb e)
      obtain ⟨A, colour, hA⟩ := hRem c0
      let shiftA : Fin nTail ↪o Fin (nRem + 1) := A.trans (Fin.succOrderEmb nRem)
      let cTail : (Fin (k + 1) ↪o Fin nTail) → κ := fun e ↦ c (e.trans shiftA)
      obtain ⟨Xtail, dtail, hXtail⟩ := hTail cTail
      let X : Fin (T + 1) ↪o Fin (nRem + 1) := prependZeroOrderEmb (Xtail.trans A)
      let d : Fin (T + 1) → κ := Fin.cases colour dtail
      refine ⟨X, d, ?_⟩
      intro e
      by_cases hzero : e 0 = 0
      · let etail : Fin k ↪o Fin T := tailOrderEmbOfZero e hzero
        have heq : e.trans X = prependZeroOrderEmb ((etail.trans Xtail).trans A) := by
          ext i
          cases i using Fin.cases with
          | zero => simp [X, hzero]
          | succ i =>
              simp only [RelEmbedding.coe_trans, Function.comp_apply]
              rw [← succ_tailOrderEmbOfZero e hzero i]
              rfl
        rw [heq]
        change c0 ((etail.trans Xtail).trans A) = d (e 0)
        rw [hA (etail.trans Xtail)]
        simp [d, hzero]
      · let epred : Fin (k + 1) ↪o Fin T := predOrderEmbOfPositive e hzero
        have heq : e.trans X = (epred.trans Xtail).trans shiftA := by
          ext i
          simp only [RelEmbedding.coe_trans, Function.comp_apply]
          rw [← succ_predOrderEmbOfPositive e hzero i]
          rfl
        rw [heq]
        change cTail (epred.trans Xtail) = d (e 0)
        rw [hXtail epred]
        obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hzero
        have hpred : epred 0 = i := by
          apply Fin.succ_injective _
          rw [succ_predOrderEmbOfPositive]
          exact hi.symm
        rw [hpred, ← hi]
        simp [d]

/-- The unique increasing tuple with empty domain. -/
def emptyOrderEmb (n : ℕ) : Fin 0 ↪o Fin n :=
  OrderEmbedding.ofStrictMono Fin.elim0 (by
    intro i
    exact Fin.elim0 i)

/-- A quantitative finite pigeonhole principle in increasing-tuple form. -/
theorem exists_constant_orderEmb {κ : Type*} [Fintype κ] [Nonempty κ]
    {T l : ℕ} (d : Fin T → κ)
    (hlarge : Fintype.card κ * (l - 1) < T) :
    ∃ J : Fin l ↪o Fin T, ∃ colour : κ, ∀ i, d (J i) = colour := by
  classical
  by_cases hl : l = 0
  · subst l
    exact ⟨emptyOrderEmb T, Classical.choice inferInstance, fun i ↦ Fin.elim0 i⟩
  have hfiber : ∃ colour : κ,
      l ≤ (Finset.univ.filter fun i : Fin T ↦ d i = colour).card := by
    by_contra h
    push Not at h
    have hle : ∀ colour : κ,
        (Finset.univ.filter fun i : Fin T ↦ d i = colour).card ≤ l - 1 := by
      intro colour
      exact Nat.le_pred_of_lt (h colour)
    have hsum :
        (∑ colour : κ, (Finset.univ.filter fun i : Fin T ↦ d i = colour).card) = T := by
      simpa using
        (Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset (Fin T)) (Finset.univ : Finset κ) d)
    have hbound : T ≤ Fintype.card κ * (l - 1) := by
      rw [← hsum]
      calc
        (∑ colour : κ,
            (Finset.univ.filter fun i : Fin T ↦ d i = colour).card) ≤
            ∑ _colour : κ, (l - 1) :=
          Finset.sum_le_sum (fun colour _ ↦ hle colour)
        _ = Fintype.card κ * (l - 1) := by simp
    exact (Nat.not_le_of_lt hlarge) hbound
  obtain ⟨colour, hcolour⟩ := hfiber
  obtain ⟨I, hIsub, hIcard⟩ := Finset.exists_subset_card_eq hcolour
  let J : Fin l ↪o Fin T := I.orderEmbOfFin hIcard
  refine ⟨J, colour, fun i ↦ ?_⟩
  have hiI : J i ∈ I := Finset.orderEmbOfFin_mem I hIcard i
  exact (Finset.mem_filter.mp (hIsub hiI)).2

/-- Finite Ramsey theorem for colourings of increasing uniform hyperedges. -/
theorem finiteHypergraphRamsey (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∀ k l : ℕ, ∃ n : ℕ, l ≤ n ∧
      ∀ c : (Fin k ↪o Fin n) → κ,
        ∃ H : Fin l ↪o Fin n, OrderedTupleHomogeneous c H := by
  intro k
  induction k with
  | zero =>
      intro l
      refine ⟨l, le_rfl, fun c ↦ ?_⟩
      let H : Fin l ↪o Fin l := (OrderIso.refl (Fin l)).toOrderEmbedding
      refine ⟨H, c (emptyOrderEmb l), fun e ↦ ?_⟩
      have he : e.trans H = emptyOrderEmb l := by
        ext i
        exact Fin.elim0 i
      rw [he]
  | succ k ih =>
      intro l
      by_cases hl : l = 0
      · subst l
        refine ⟨0, le_rfl, fun c ↦ ?_⟩
        refine ⟨(OrderIso.refl (Fin 0)).toOrderEmbedding,
          Classical.choice inferInstance, fun e ↦ ?_⟩
        exact Fin.elim0 (e 0)
      · let T : ℕ := Fintype.card κ * (l - 1) + 1
        obtain ⟨n, hTn, hn⟩ := exists_leastIndexCanonical k ih T
        refine ⟨n, ?_, fun c ↦ ?_⟩
        · have hcard : 1 ≤ Fintype.card κ := Fintype.card_pos
          have hlT : l ≤ T := by
            calc
              l = 1 * (l - 1) + 1 := by omega
              _ ≤ Fintype.card κ * (l - 1) + 1 := by
                exact Nat.add_le_add_right (Nat.mul_le_mul_right (l - 1) hcard) 1
              _ = T := rfl
          exact hlT.trans hTn
        · obtain ⟨X, d, hX⟩ := hn c
          have hlarge : Fintype.card κ * (l - 1) < T := by
            simp [T]
          obtain ⟨J, colour, hJ⟩ := exists_constant_orderEmb d hlarge
          refine ⟨J.trans X, colour, fun e ↦ ?_⟩
          have hcanon := hX (e.trans J)
          have hcolour := hJ (e 0)
          simpa only [RelEmbedding.trans_assoc] using hcanon.trans hcolour

/-- Threshold form: the same Ramsey number works in every larger finite ordered ambient set. -/
theorem finiteHypergraphRamsey_ge (κ : Type*) [Fintype κ] [Nonempty κ]
    (k l : ℕ) :
    ∃ n₀ : ℕ, l ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ c : (Fin k ↪o Fin n) → κ,
        ∃ H : Fin l ↪o Fin n, OrderedTupleHomogeneous c H := by
  obtain ⟨n₀, hln₀, hn₀⟩ := finiteHypergraphRamsey κ k l
  refine ⟨n₀, hln₀, fun n hn c ↦ ?_⟩
  let inclusion : Fin n₀ ↪o Fin n := Fin.castLEOrderEmb hn
  let c₀ : (Fin k ↪o Fin n₀) → κ := fun e ↦ c (e.trans inclusion)
  obtain ⟨H₀, colour, hH₀⟩ := hn₀ c₀
  refine ⟨H₀.trans inclusion, colour, fun e ↦ ?_⟩
  have he := hH₀ e
  change c ((e.trans H₀).trans inclusion) = colour at he
  simpa only [RelEmbedding.trans_assoc] using he

end

end MomentAmbiguity
